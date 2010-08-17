#!/usr/bin/python
# -*- coding: utf-8  -*-
from __future__ import division


"""
Python MediaWiki Dump Analysis Toolkit
Cleaned up version of the MediaWiki Dump Analysis code from the wredese project.

Requirements:
    * Python 2.6+, Linux;
    * PyWikipedia?/Trunk ( http://svn.wikimedia.org/svnroot/pywikipedia/trunk/pywikipedia/ ) 

Input Alternatives:
    * Wikipedia history dump (e.g. enwiki-20100130-pages-meta-history.xml.7z);
    * Wikipedia page(s) name / category;
    * Wikipedia page(s) history (.xml/.7z/.bz2/.gz). 

Input Processing:
    * Detects reverts, reverted edits, revert wars, self-reverts;
    * Filtering, labeled revisions data sets management, etc;
    * Calculates users/page counters, revert rates, page diffs, etc (~1 week/C2Duo/Full English Wikipedia dump). 

Usage
=====

--------------        ----------          -----------------      ---------
| *.xml(.7z) |   =>   |  .pkl  |     =>   | .pkl.filtered |  =>  | .revs |
--------------        ----------          -----------------      ---------
                          ||                                      
                          \/
                  ------------------
                  | counters.split |                                ||
                  ------------------                                ||
                          ||                                        ||
                          \/                                        \/
                  ------------------
                  | counters.megred |
                  ------------------
                          ||                            -------------------
                          \/                            |                 |
                  ---------------------                 |   Processing    |
                  | counters.filtered |          =>     |                 |
                  ---------------------                 -------------------





Note: use "> progress.txt 2>&1 &"

Generating corpus (.pkl) from an xml dump(s):
r.py -compute-pkl -xml:data/Rocket*.7z -output:data/Rocket.pkl
r.py -compute-pkl -xml:../enwiki-20100130-pages-meta-history.xml.7z -output:data/enwiki-20100130-pages-meta-history.pkl


Filtering interesting/known revisions, reverts analysis, producing .revs files:
./r.py -filter-known-revisions -pkl:data/Rocket.pkl -output:data/Rocket.revs
./r.py  -filter-known-revisions -pkl:p/enwiki-20100130-pages-meta-history.pkl -output:p/pan-wvc-10.revs


Analyzing corpus (.pkl):
./r.py -pkl:p/pan-wvc-10.full -counters:p/ratings-enwiki-20100130.merged -analyze:decisiontree -vvv

Computing user counters:
./r.py -pkl:/data/enwiki-20100130.none.full -compute-counters -output:p/counters-enwiki-20100130.none.full.split > progress-counters-enwiki-20100130.none.full.split.txt 2>&1 &

Filtering corpus:
./r.py -pkl:/data/enwiki-20100130.none.full -filter-pkl -output:p/pan-wvc-10.none.full > progress-wvc-filter.none.full.txt 2>&1 &


Filtering known revisions/producing .known files:
./r.py -pkl:p/pan-wvc-10.none.full -filter-known-revisions -output:p/pan-wvc-10.none.known
./r.py -pkl:p/Rocket.none.full -filter-known-revisions -output:p/enwiki.Rocket.none.known

Merging counters:
./r.py -counters:p/counters-enwiki-20100130.none.full.split -output:counters-enwiki-20100130.none.full.merged

Filtering counters:
./r.py -counters:p/counters-enwiki-20100130.pan10.merged -revisions:p/pan-wvc-10.test-corpus.none.known -output:p/counters-enwiki-20100130.pan10-test.filtered
./r.py -counters:p/counters-enwiki-20100130.pan10.filtered -pkl:p/Rocket.full -output:p/counters-enwiki-20100130.pan10-test.filtered


&params;
    -xml           Retrieve information from a local XML dump(s) (pages-articles
                   or pages-meta-current, see http://download.wikimedia.org).
                   Argument can be given as "-xml:filename_pattern".

...


All other parameters will be regarded as part of the title of a single page,
and the bot will only work on that single page.
"""

__version__='$Id: r.py 7909 2010-02-05 06:42:52Z Dc987 $'

import re, sys, time, calendar, difflib, string, math, hashlib 
import os, fnmatch, copy, pprint, cPickle
from collections import defaultdict, namedtuple 
from operator import itemgetter

# Needs Python 2.7 or http://code.activestate.com/recipes/576693/
from ordereddict import OrderedDict

# pywikipedia (trunk 2010/03/15) in your PYTHONPATH, configured and running
import wikipedia, pagegenerators, xmlreader, editarticle

import ddiff


NNN = 313797035 # total revisions in the wiki dump

# Counters helpers
counters_dict = lambda:defaultdict(lambda:(0, 0, 0, 0, 0, 0, 0))
good_counter = lambda x:x[-2]*5<x[0]



# Helpers
def locate(pattern):
    '''Locate all files matching supplied filename pattern in and below
    supplied root directory.'''
    (root, pattern) = os.path.split(pattern)
    if not root: root = os.curdir
    for path, dirs, files in os.walk(os.path.abspath(root)):
        for filename in fnmatch.filter(files, pattern):
            yield os.path.join(path, filename)


def timestamp_to_time(timestamp):
    '''Wikipedia format timestamp to unix time'''
    year = int(timestamp[0:4])
    month = int(timestamp[5:7])
    day = int(timestamp[8:10])
    hour = int(timestamp[11:13])
    min = int(timestamp[14:16])
    sec = int(timestamp[17:19])
    return calendar.timegm((year, month, day, hour, min, sec))




# TODO:
# * remove junk symbols?
def compute_pkl(xmlFilenames):
        use _output_arg to output diffs, md5s and metainfo to .pkl file'''

    if(_output_arg):
        FILE = open(_output_arg, 'wb')

    # separators between tokens
    p = re.compile(r'\, |\. |\s+')

    total_revisions = 0; start = time.time(); full_info = None; fake_id = -1; prev_title = None;
    al = []; bl = []; bid = None; asndiff = []; bsndiff = []; bndiffid = None
    for xmlFilename in xmlFilenames:
        dump = xmlreader.XmlDump(xmlFilename, allrevisions=True)
        revisions = dump.parse()
        for e in revisions:
            total_revisions += 1
            
            # Encode everything in utf-8. This saves space, time and memory. 
            if(e.text):     e.text = e.text.encode('utf-8')
            if(e.comment):  e.commment = e.comment.encode('utf-8')
            if(e.username): e.username = e.username.encode('utf-8')
            if(e.title):    e.title = e.title.encode('utf-8')
            
            # Catch new pages | page revisions
            # Isolate and process pages without ids
            try:
                id = int(e.id)
                prev_title = None
            except:                 # process pages without id
                if(e.title != prev_title): fake_id -= 1;
                prev_title = e.title
                id = fake_id;

            if(id == bid):          # still analyzing the same page....
                al = bl             # bl - previous revision text (split into lines)
            else: 
                al = []; bid = id; DT = (time.time() - start) / 3600;
                wikipedia.output("R %d T %f ETA %f : %d %s %s %s" % 
                    (total_revisions, DT, (NNN - total_revisions) / total_revisions * DT, id, e.id, e.revisionid, e.title))
            bl = e.text.splitlines()

            # merge (removed, added) lines and split them into tokens (a, b)
            # a - tokens from the al (removed), b - tokens from the bl (added)
            # ilA - number of added (new) lines, 
            # ilR - number of removed lines
            (d, dposl) = ddiff.ddiff(al, bl)     # calculate ddiff for lines
            a = []; b = []; ilA = 0; ilR = 0; ilM = 0;
            for t, v in d.items():
                if(v > 0 and ilA < 5): b.extend(p.split(t)); ilA += 1
                elif(v < 0 and ilR < 5): a.extend(p.split(t)); ilR += 1
                else: ilM += 1

            if(_output_arg):
                (d, dposw) = ddiff.ddiff(a, b); iwA = 0; iwR = 0; iwM = 0
                diff = []
                for t, v in d.items():
                    if(v > 0 and iwA < 50): diff.append((t, v)); iwA += 1
                    elif(v < 0 and iwR < 50): diff.append((t, v)); iwR += 1
                    else: iwM += 1

                # calculate page text hashes (have nothing to do with diffs)
                digest = None
                if(e.text):
                    m = hashlib.md5(e.text)
                    digest = m.digest()

                try:
                    full_info = (id, int(e.revisionid), e.username, e.comment, e.title, 
                            len(e.text), timestamp_to_time(e.timestamp), digest, e.ipedit,
                            e.editRestriction, e.moveRestriction, e.isredirect,
                            len(al), len(bl), dposl[0], dposl[1], dposl[2], 
                            ilA, ilR, iwA, iwR, ilM, iwM, diff)
                    cPickle.dump(full_info, FILE, -1)
                except:
                    wikipedia.output("Error at: %s %s %s %s" % (e.id, e.revisionid, e.title, e.timestamp))           
    wikipedia.output("%f seconds, %d revisions" % (time.time() - start, total_revisions))


def dump_cstats(stats):
    def key(v):
        if len(v[1]) < 2: return 0
        return min(v[1].values())

    ids.dump()

    sstats = OrderedDict(sorted(copy.deepcopy(stats).items(), key = key, reverse=True))
    for s, v in sstats.iteritems():
        total = sum(v.values()); ss = "";
        for k, i in v.iteritems(): 
            v[k] = "%d (%d%%)" % (i, i*100/total)
            if k=='bad' and s.find('good') > -1: v[k] = mark(v[k])
            ss += "%s:%s  " % (k, v[k])
            if len(ss) > 80: ss += "\n%-60s:" % ""
        sstats[s] = ss

    wikipedia.output("===================================================================================")
    for k, v in sstats.iteritems(): wikipedia.output("%-60s:%s" % (k, v))
    wikipedia.output("===================================================================================")



def display_pkl():
    FILE = open(_pkl_arg, 'rb')
    total_revisions = 0; total_pages = 0; 
    start = time.time()
    try:
        while True:
            info = cPickle.load(FILE)
            total_revisions += 1
            wikipedia.output(str(info))
    except IOError, e:
        raise
    except EOFError, e:
        wikipedia.output("Revisions %d. Analysis time: %f" % (total_revisions, time.time() - start))



class FullInfo(object):
    __slots__ = ('i', 'reverts_info', 'rev_score_info', 'duplicates_info', 'reverted', 'edit_group', 'oldid',                 
                 'id', 'revid', 'username', 'comment', 'title', 'size', 'utc', 'md5', 'ipedit',
                 'editRestriction', 'moveRestriction', 'isredirect',
                 'al', 'bl', 'lo', 'ahi', 'bhi', 'ilA', 'ilR', 'iwA', 'iwR', 'ilM', 'iwM', 'diff'
                  )

    def __init__(self, args):
        (self.id, self.revid, self.username, self.comment, self.title,
        self.size, self.utc, self.md5, self.ipedit,
        self.editRestriction, self.moveRestriction, self.isredirect,
        self.al, self.bl, self.lo, self.ahi, self.bhi,
        self.ilA, self.ilR, self.iwA, self.iwR, self.ilM, self.iwM, self.diff) = args

        self.reverts_info = -1
        self.rev_score_info = 0
        self.duplicates_info = None
        self.reverted = None
        self.edit_group = []
        self.oldid = None


class EmptyFullInfoPlaceholder(object):
    def __init__(self):
        self.username = None
        self.edit_group = None
        self.revid = None


def read_pkl():
    pklFilenames = sorted(locate(_pkl_arg))
    wikipedia.output(u"Files: \n%s\n\n" % pklFilenames)

    for pklFilename in pklFilenames:
        wikipedia.output("Reading %s..." % pklFilename)
        FILE = open(pklFilename, 'rb')
        start = time.time(); size = os.path.getsize(pklFilename); show_progress = time.time() + 15
        revisions = [];
        try:
            info = FullInfo(cPickle.load(FILE))     # load first in order to  
            id = info.id;                           # initialize id from info.id
            revisions.append(info)
            while True:
                info = FullInfo(cPickle.load(FILE))
                if(id != info.id):
                    yield revisions
                    revisions = []
                    id = info.id

                    if(time.time() > show_progress):
                        DT = (time.time() - start) / 3600; BPH = FILE.tell() / DT; show_progress = time.time() + 15
                        wikipedia.output("DT %f Hours, ETA %f Hours." % (DT, (size/BPH - DT)) )

                revisions.append(info)
        except IOError, e:
            raise
        except EOFError, e:            
            wikipedia.output("Done reading %s. Read time: %f." % (pklFilename, time.time() - start))
            yield revisions


def filter_pkl():
    """ """
    total_pages = 0
    FILE = open(_output_arg, 'wb')
    start = time.time()
    total_pages = 0; total_revisions = 0;
    filtered_pages = 0; filtered_revisions = 0;

    for revisions in read_pkl():
        total_pages += 1;
        total_revisions += len(revisions)
        if(total_pages%100 == 0):
            wikipedia.output("Page %d. Revs %d. Filtered Pages %d. Filtered Revs %d. " %
                (total_pages, total_revisions, filtered_pages, filtered_revisions))
        
        # Add your own filter. e.g e.utc > 1258329600
        # if e.utc > 1258329600: continue
        if False: continue        

        for e in revisions:
            full_info = (e.id, e.revid, e.username, e.comment, e.title,
                e.size, e.utc, e.md5, e.ipedit,
                e.editRestriction, e.moveRestriction, e.isredirect,
                e.al, e.bl, e.lo, e.ahi, e.bhi,
                e.ilA, e.ilR, e.iwA, e.iwR, e.ilM, e.iwM, e.diff)
            cPickle.dump(full_info, FILE, -1)
            filtered_revisions += 1
        filtered_pages += 1

    print "Filtered pages: ", filtered_pages, "Filtered revisions", filtered_revisions


def referenced_users(revisions, users = {}):
    """Returns the list of referenced in the revisions users"""
    for e in revisions:
        users[e.username] = True
        if e.reverted: users[e.reverted.username] = True
        for g in e.edit_group:
            users[g.username] = True
            if g.reverted: users[g.reverted.username] = True
    return users    
    


def read_counters(revisions):
    """Read/Merge/Filter user counters. 
    If _output_arg global is provided, counters will be merged and saved;
    If revisions argument is provided only referenced users revisions will be saved;"""
    
    wikipedia.output("Reading %s..." % _counters_arg)
    FILE = open(_counters_arg, 'rb')
    user_counters = counters_dict()
    start = time.time()
    try:
        if _output_arg and not _analyze_arg and not _train_arg:  # read and merge
            users = {}
            if revisions:                               
                referenced_users(revisions, users)               # filter / known users (use known revisions)            
            if _pkl_arg:                                        
                for revisions in read_pkl():
                    analyze_reverts(revisions)
                    referenced_users(revisions, users)           # filter / known users (use .pkl)
                                                
            while True:
                (u,r) = cPickle.load(FILE)
                if not revisions or u in users:
                    user_counters[u] = tuple([a+b for (a,b) in zip(user_counters[u] , r)])
        else:                                           
           while True:                                  # just read
               (u,r) = cPickle.load(FILE)
               user_counters[u] = r

    except IOError, e:
        raise
    except EOFError, e:
        wikipedia.output("Done reading %s. Read time: %f. Total users: %d" % (_counters_arg, time.time() - start, len(user_counters)))
    if(_output_arg and not _analyze_arg and not _train_arg):
        #wikipedia.output("Filtering counters <0 or >10")
        FILE = open(_output_arg, 'wb')
        for u, r in user_counters.iteritems():
            # if(r < 0 or r > 10):
            cPickle.dump((u, r), FILE, -1)
    return user_counters



# -------------------------------------------------------------------------
# initializes: revisions[].reverts_info
# -1  : regular revision
# -2 : between duplicates, by single user (reverted, most likely bad)
# -3 : between duplicates, by other users (reverted, questionable)
# -4 : between duplicates, (revert that was reverted. revert war.)
# -5 : self-revert
# >=0: this revision is a duplicate of
# -------------------------------------------------------------------------
def reverts_info_descr(e):
    if e.i == e.reverts_info: return "regular revision (have duplicates)"    
    if e.i < e.reverts_info: return "regular revision (< e.reverts_info ?)"
    if e.reverts_info > 0: return "regular revert (a duplicate of a previous revision)"
    if e.reverts_info < -5: return "regular revision (< -5 ?)"

    return( "regular revision (duplicate of the first revision)",               #  0            
            "between duplicates, reverted (self-reverted)",                     # -5 
            "between duplicates, revert that was reverted (revert war)",        # -4 
            "between duplicates, by other users (reverted, questionable)",      # -3
            "between duplicates, by single user (reverted, most likely bad)",   # -2 
            "regular revision"                                                  # -1
            )[e.reverts_info]
                        
def urri(ri):
    if(ri > -1): return 'revert'
    return ('self_revert', 'revert_war', 'questionable', 'reverted', 'regular')[ri]
                        
                        
def analyze_reverts(revisions):
    rev_hashes = defaultdict(list)      # Filling md5 hashes map (md5 -> [list of revision indexes]) for nonempty
    user_revisions = defaultdict(int)   # Filling nuber of nonempty revisions made by user
    total_revisions = len(revisions)

    for i, e in enumerate(revisions):
        # calculate page text hashes and duplicates lists
        if(e.md5):
            rev_hashes[e.md5].append(i)
            user_revisions[e.username] += 1;
        e.i = i

    # Marking duplicates_info:
    #   None: regular revision
    #   [revid, revid, ]: this revision is a duplicate of
    for m, indexes in rev_hashes.iteritems():
        if len(indexes) > 1:
            for i in indexes:
                revisions[i].duplicates_info = indexes

    # Marking (-2, -4, >=0)
    # -2 : between duplicates, by single user (reverted, most likely bad)
    # -4 : between duplicates, (revert that was reverted. revert war.)
    # ------------------------------------------------------------------
    # Revision 54 (-1)      User0    Regular edit
    # Revision 55 (55)      User1    Regular edit
    # Revision 56 (-2)      User2    Vandalism
    # Revision 57 (-2)      User2    Vandalism
    # Revision 58 (-2)      User3    Correcting vandalism, but not quite
    # Revision 59 (55)      User4    Revert to Revision 55

    revert = None
    for e in reversed(revisions):
        if revert != None:
            if not e.duplicates_info:                           # regular reverted revision
                e.reverts_info = -2      
                e.reverted = revert
            elif e.i == revert.duplicates_info[0]:              # reached reverted_to[0]
                e.reverts_info = e.i                            # LEGACY 
                revert = None
            elif e.duplicates_info != revert.duplicates_info:   # revert war, revision has duplicates and was reverted 
                e.reverts_info = -4 
                e.reverted = revert
            else:
                revert = e
                e.reverts_info = revert.duplicates_info[0]      # LEGACY 
        elif e.duplicates_info:
            if e.i == e.duplicates_info[0]:
                e.reverts_info = e.i                            # LEGACY 
                revert = None
            else:                 
                revert = e
                e.reverts_info = revert.duplicates_info[0]      # LEGACY
                    

    # Marking (-3) : between duplicates, by other users (reverted, questionable)
    # Revision 54 (-1)  ->   (-1)                User0    Regular edit
    # Revision 55 (55)  ->   (55)                User1    Regular edit
    # Revision 56 (-2)  ->   (-2)                User2    Vandalism
    # Revision 57 (-2)  ->   (-2)                User2    Vandalism
    # Revision 58 (-2)  ->   (-3)                User3    Correcting vandalism, but not quite
    # Revision 59 (55)  ->   (55)                User4    Revert to Revision 55

    # Marking (-5) : self-reverts
    # Revision 54 (-1)  ->   (-1)                User0    Regular edit
    # Revision 55 (55)  ->   (55)                User1    Regular edit
    # Revision 56 (-2)  ->   (-2)                User1    Self-reverted edit
    # Revision 59 (55)  ->   (55)                User4    Revert to Revision 55
         
    username = None; prev = EmptyFullInfoPlaceholder();
    for e in revisions:
        if(e.reverts_info == -2):
            if(e.username == e.reverted.username): e.reverts_info = -5
            if(username == None): username = e.username
            elif (username != e.username): e.reverts_info = -3
        else: username = None

        # Filling oldid
        e.oldid = prev.revid

        # Marking edit groups: consequent edits by a single user
        if prev.username == e.username:
            prev.edit_group.append(prev)  
            e.edit_group = prev.edit_group
        elif prev.edit_group:
            prev.edit_group.append(prev)
        
        prev = e        




def mark(value, function = None):
    if(not function):
        return "\03{lightpurple}%s\03{default}" % unicode(value)

    if(function(value) == True): return "\03{lightgreen}%s\03{default}" % unicode(value)
    if(function(value) == False): return "\03{lightred}%s\03{default}" % unicode(value)
    return "\03{lightpurple}%s\03{default}" % unicode(value)


def show_diff(e):
        text = "";
        marker = [' *', 
                  ' +', ' ++', ' +++', ' ++++', ' +++++',
                  ' -----', ' ----', ' ---', ' --', ' -']
        for (t, v) in e.diff:
            if(v > 5): v = 5
            elif(v < -5): v = -5
            text += mark(marker[v] + t, lambda x:x[1]=='-');

        wikipedia.output(text)
        wikipedia.output("Old: %s lines. New: %s lines." % (e.al, e.bl))
        wikipedia.output("Added: %d lines, %d words" % (e.ilA, e.iwA))
        wikipedia.output("Removed: %d lines, %d words" % (e.ilR, e.iwR))
        wikipedia.output("Diff position: lo = %d, ahi = %d, bhi = %d" % (e.lo, e.ahi, e.bhi))

def show_edit(e, prefix):
    wikipedia.output("%s %d (%s) by %s: \03{lightblue}%s\03{default}  Diff: http://en.wikipedia.org/w/index.php?diff=%d <<< " %   \
     (prefix, e.i, mark(e.reverts_info, lambda x:x!=-2), e.username, e.comment, e.revid))

def show_edit_ex(e, extra):
    wikipedia.output("\n\n\n\n\n\n\n >> R%d (%s) by %s: \03{lightblue}%s\03{default}  Diff: http://en.wikipedia.org/w/index.php?diff=%d <<< " %   \
         (e.i, mark(e.reverts_info, lambda x:x!=-2), e.username, e.comment, revid))
    if(e.reverted): show_edit(e.reverted, "Reverted:")
    if(e.edit_group):
        for edit in e.edit_group: show_edit(edit, "Edit Group:")
        wikipedia.output("Edit Group Diff: http://en.wikipedia.org/w/index.php?diff=%d&oldid=%s" % (e.edit_group[-1].revid, e.edit_group[0].oldid))
            
    show_diff(e)
    if(extra): extra()


def analyze_comment(comment):
    """Comment heuristics. NOTE: use .decode("utf-8")!"""
    #if(e.username.lower().find('bot') > -1):

    if(comment):
        if comment.startswith('[[WP:'):
            if comment.startswith(u'[[WP:UNDO|Undid'): return 'undo', "Starts with [[WP:UNDO|Undid"
            elif comment.startswith(u'[[WP:A'):
                if comment.startswith(u'[[WP:AES|\u2190]]Replaced'): return 'replaced', "Starts with [[WP:AES|\u2190]]Replaced"
                elif comment.startswith(u'[[WP:AES|\u2190]]Redirected'): return 'redirected', "Starts with [[WP:AES|\u2190]]Redirected"
                elif comment.startswith(u'[[WP:AES|\u2190]]Blanked'): return 'blanked', "Starts with [[WP:AES|\u2190]]Blanked"
                elif comment.startswith(u'[[WP:AES|\u2190]]Undid'):  return 'undid', "Starts with [[WP:AES|\u2190]]Undid"
                elif comment.startswith(u'[[WP:AES|\u2190]]Reverted'): return 'reverted', "Starts with [[WP:AES|\u2190]]Reverted"
                elif comment.startswith(u'[[WP:AES|\u2190]] Replaced'): return 'replaced', "Starts with [[WP:AES|\u2190]] Replaced"
                elif comment.startswith(u'[[WP:AES|\u2190]] Redirected'): return 'redirected', "Starts with [[WP:AES|\u2190]] Redirected"
                elif comment.startswith(u'[[WP:AES|\u2190]] Blanked'): return 'blanked', "Starts with [[WP:AES|\u2190]] Blanked"
                elif comment.startswith(u'[[WP:AES|\u2190]] Undid'): return 'undid', "Starts with [[WP:AES|\u2190]] Undid"
                elif comment.startswith(u'[[WP:AES|\u2190]] Reverted'): return 'reverted', "Starts with [[WP:AES|\u2190]] Reverted"
                elif comment.startswith(u'[[WP:AES|\u2190]]\u200bReplaced'): return 'replaced', "Starts with [[WP:AES|\u2190]]\u200bReplaced"
                elif comment.startswith(u'[[WP:AES|\u2190]]\u200bRedirected'): return 'redirected', "Starts with [[WP:AES|\u2190]]\u200bRedirected"
                elif comment.startswith(u'[[WP:AES|\u2190]]\u200bBlanked'): return 'blanked', "Starts with [[WP:AES|\u2190]]\u200bBlanked"
                elif comment.startswith(u'[[WP:AES|\u2190]]\u200bUndid'): return 'undid', "Starts with [[WP:AES|\u2190]]\u200bUndid"
                elif comment.startswith(u'[[WP:AES|\u2190]]\u200bReverted'): return 'reverted', "Starts with [[WP:AES|\u2190]]\u200bReverted"
                elif comment.startswith(u'[[WP:AES|\u2190Replaced'): return 'replaced', "Starts with [[WP:AES|\u2190Replaced"
                elif comment.startswith(u'[[WP:AES|\u2190Redirected'): return 'redirected', "Starts with [[WP:AES|\u2190Redirected"
                elif comment.startswith(u'[[WP:AES|\u2190Blanked'): return 'blanked', "Starts with [[WP:AES|\u2190Blanked"
                elif comment.startswith(u'[[WP:AES|\u2190Undid'): return 'undid', "Starts with [[WP:AES|\u2190Undid"
                elif comment.startswith(u'[[WP:AES|\u2190Reverted'): return 'reverted', "Starts with [[WP:AES|\u2190Reverted"
                elif comment.startswith(u'[[WP:Automatic edit summaries|\u2190]]Replaced'): return 'replaced',  "Starts with [[WP:Automatic edit summaries|\u2190]]Replaced"
                elif comment.startswith(u'[[WP:Automatic edit summaries|\u2190]]Redirected'): return 'redirected', "Starts with [[WP:Automatic edit summaries|\u2190]]Redirected"
                elif comment.startswith(u'[[WP:Automatic edit summaries|\u2190]]Blanked'): return 'blanked', "Starts with [[WP:Automatic edit summaries|\u2190]]Blanked"
                elif comment.startswith(u'[[WP:Automatic edit summaries|\u2190]]Undid'): return 'undid', "Starts with [[WP:Automatic edit summaries|\u2190]]Undid"
                elif comment.startswith(u'[[WP:Automatic edit summaries|\u2190]]Reverted'): return 'reverted', "Starts with [[WP:Automatic edit summaries|\u2190]]Reverted"
                elif comment.startswith(u'[[WP:AWB'): return 'awb', "Starts with [[WP:AWB"
                elif comment.startswith(u'[[WP:AES'): return 'aes', "Starts with [[WP:AES"
                else: return 'wp', "Starts with WP"
            elif comment.startswith(u'[[WP:UNDO|Revert'): return 'revert', "Starts with [[WP:UNDO|Revert"
            elif comment.startswith(u'[[WP:RBK|Reverted'): return 'reverted', "Starts with [[WP:RBK|Reverted"
            #elif comment.startswith(u'[[Help:': return 'help'    
            else: return 'wp', "Starts with WP"  #print e.comment.encode('unicode-escape');
        elif(comment[-2:] == '*/'): return 'section', "No comment/section"
        else:
            if comment.startswith('Revert'): return 'revert', "Starts with revert"
            elif comment.startswith('Undid'): return 'undid', "Starts with undid"
            elif comment.startswith('rvv'): return 'rvv', "Starts with rvv"
            elif comment.startswith('rev'): return 'rev', "Starts with rev"
            elif comment.startswith('rv'): return 'rv', "Starts with rv"
            elif comment[:4] in ('BOT ', 'bot ', 'robo', 'Robo'): return 'bot', "Starts with BOT, bot, robo, Robo"
            elif comment.startswith('cat'): return 'cat', "Starts with cat"
            elif comment.startswith('+'): return 'plus', "Starts with plus"
            elif comment.find('spam') > -1: return 'spam',  "Starts with spam"
            elif comment.find('ref') > -1: return 'ref',  "Starts with ref"
            elif comment.startswith(r'http://'): return 'bad', "Starts with http"
            elif comment.startswith(r'HTTP://'): return 'bad', "Starts with HTTP"
            elif comment.startswith(r'WWW'): return 'bad', "Starts with WWW"
            elif comment.startswith(r'www'): return 'bad', "Starts with www"

            return 'unknown', "Probably Ok"
            # if len(comment) > 80:        # we like long comments
            # if(len(e.comment.split()) > 7): add_uefeature('comment_long')
    return 'no', "No comment"





def compute_counters(revisions, user_counters):
    """Update users counters for revisions"""
    for e in revisions:
        if e.reverts_info > -1: b =    (1, 1, 0, 0, 0, 0, 0)
        elif e.reverts_info == -1: b = (1, 0, 0, 0, 0, 0, 1)
        elif e.reverts_info == -2: b = (1, 0, 0, 0, 0, 1, 0)
        elif e.reverts_info == -3: b = (1, 0, 0, 0, 1, 0, 0)
        elif e.reverts_info == -4: b = (1, 0, 0, 1, 0, 0, 0)
        elif e.reverts_info == -5: b = (1, 0, 1, 0, 0, 0, 0)
        else: b = (1, 0, 0, 0, 0, 0, 0)
        user_counters[e.username] = array.array('i', [a+b for (a,b) in zip(user_counters[e.username] , b)])



def compute_counters_dictionary():
    """Compute users counters for .pkl"""
    user_counters = counters_dict()

    if(_output_arg):
        FILE = open(_output_arg, 'wb')

    total_pages = 0; total_revisions = 0; start = time.time();
    for revisions in read_pkl():
        analyze_reverts(revisions)
        compute_counters(revisions, user_counters)
        total_pages += 1;
        total_revisions += len(revisions)

        if(total_pages%1000 == 0):
            wikipedia.output("Page %d. Revisions %d. Users %s. Analysis time: %f. " %
                (total_pages, total_revisions, len(user_counters), time.time() - start))

            for u, r in user_counters.iteritems():
                cPickle.dump((u, r), FILE, -1)
            user_counters = counters_dict()

    if(_output_arg):
        for u, r in user_counters.iteritems():
            cPickle.dump((u, r), FILE, -1)


def compute_revisions_list():
    """Analyze reverts and compute revisions list"""
    revisions_list = []
    for revisions in read_pkl():
        analyze_reverts(revisions)
        
        # A good place to filter revisions of interest
        revisions_list.extend(revisions)            

    if(_output_arg): 
        cPickle.dump(revisions_list, open(_output_arg, 'wb'), -1); 
        wikipedia.output("Done. %d revisions have been filtered." % len(revisions_list))



def main():
    global _analyze_arg,
    global _verbose_arg, _output_arg, _pkl_arg, _counters_arg;
     
    _xml_arg = None; _pkl_arg = None; _compute_pkl_arg = None; 
    _display_pkl_arg = None; _compute_counters_arg = None;_output_arg = None; _analyze_arg = ""; _train_arg = ""
    _counters_arg = None; _username_arg = None; _filter_pkl_arg = None; _count_empty_arg = None
    _revisions_arg = None; _evaluate_arg = None
    
    
    stats = defaultdict(lambda:defaultdict(int)); revisions = [];

    for arg in wikipedia.handleArgs():
        if arg.startswith('-xml') and len(arg) > 5: _xml_arg = arg[5:]
        if arg.startswith('-pkl') and len(arg) > 5: _pkl_arg = arg[5:]
        if arg.startswith('-revisions') and len(arg) > 11: _revisions_arg = arg[11:]
        if arg.startswith('-counters') and len(arg) > 10: _counters_arg = arg[10:]
        if arg.startswith('-username') and len(arg) > 10: _username_arg = arg[10:]
        if arg.startswith('-retrain'): _retrain_arg = True
        if arg.startswith('-filter-pkl'): _filter_pkl_arg = True
        if arg.startswith('-output') and len(arg) > 8: _output_arg = arg[8:]
        if arg.startswith('-compute-counters'): _compute_counters_arg = True
        if arg.startswith('-compute-pkl'): _compute_pkl_arg = True
        if arg.startswith('-display-pkl'): _display_pkl_arg = True
        if arg.startswith('-analyze'): _analyze_arg = True
        if arg.startswith('-analyze') and len(arg) > 9: _analyze_arg = arg[9:] 
 

    if not _xml_arg and not _pkl_arg and not _counters_arg and not _revisions_arg:
        wikipedia.output(__doc__)
        return

    if _xml_arg:        # XML files input
        xmlFilenames = sorted(locate(_xml_arg))
        wikipedia.output(u"Files: \n%s\n\n" % xmlFilenames)
        mysite = wikipedia.getSite()
        
        
    if(_compute_pkl_arg): compute_pkl(xmlFilenames); return
    if(_display_pkl_arg): display_pkl(); return
    if(_filter_pkl_arg): filter_pkl(); return
    
    if(_compute_counters_arg): compute_counters_dictionary()
    if(_compute_revisions_arg): revisions = compute_revisions_list()

    # load precashed revisions
    if(_revisions_arg):
        wikipedia.output("Reading %s..." % _revisions_arg)
        revisions = cPickle.load(open(_revisions_arg, 'rb'))

    # load precashed counters 
    if(_counters_arg):
        user_counters = read_counters(revisions)
        if(_username_arg): 
            wikipedia.output("User %s, has_key %s, counter %s" %
                (_username_arg, user_counters.has_key(_username_arg), user_counters[_username_arg]))

    if(_analyze_arg):
        start = time.time();        
        if _analyze_arg: analyze(revisions, user_counters)
        wikipedia.output("Revisions %d. Analysis time: %f" % (len(revisions), time.time() - start))

    if stats:
        dump_cstats(stats)

if __name__ == "__main__":
    try:
        main()
    finally:
        wikipedia.stopme()

