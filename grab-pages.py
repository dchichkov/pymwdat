#!/usr/bin/python
# -*- coding: utf-8  -*-
"""
This is not a simple bot that downloads complete page histories.
The following parameters are supported:

&params;
-output           Output directory. Current directory is the default.

-dry              If given, doesn't grab pages, but only shows
                  which would have been downloaded.

All other parameters will be regarded as part of the title of a single page,
and the bot will only work on that single page.

Examples:
./grab-pages.py -dry -page:"Holy Grail"
./grab-pages.py -dry -category:"Holy Grail"
./grab-pages.py -output:./data -page:"Holy Grail"

"""
__version__ = '$Id: grab-pages.py 7845 2009-12-30 17:02:05Z xqt $'
import wikipedia as pywikibot
import xmlreader
import pagegenerators
import urllib, urllib2

# This is required for the text that is shown when you run this script
# with the parameter -help.
docuReplacements = {
    '&params;': pagegenerators.parameterHelp
}

class BasicBot:
    # Edit summary message that should be used.
    # NOTE: Put a good description here, and add translations, if possible!
    msg = {
        'ar': u'روبوت: تغيير ...',
        'cs': u'Robot změnil ...',
        'de': u'Bot: Ändere ...',
        'en': u'Robot: Changing ...',
        'fr': u'Robot: Changé ...',
        'ja':u'ロボットによる：編集',
        'ksh': u'Bot: Ännern ...',
        'nds': u'Bot: Änderung ...',
        'nl': u'Bot: wijziging ...',
        'pl': u'Bot: zmienia ...',
        'pt': u'Bot: alterando...',
        'sv': u'Bot: Ändrar ...',
        'zh': u'機器人：編輯.....',
    }

    def __init__(self, generator, dry):
        """
        Constructor. Parameters:
            * generator - The page generator that determines on which pages
                          to work on.
            * dry       - If True, doesn't do any real changes, but only shows
                          what would have been changed.
        """
        self.generator = generator
        self.dry = dry
        # Set the edit summary message
        self.summary = pywikibot.translate(pywikibot.getSite(), self.msg)

    def run(self):
        for page in self.generator:
            self.treat(page)

    def treat(self, page):
        """
        Loads the given page, does some changes, and saves it.
        """
        try:
            # Load the page
            if self.dry:
                pywikibot.output(u"\nDry Run. Title is: %s" % page.urlname())
                return
            
            limit = 1000
            offset = '1'
            total_revisions = 0
            chunk_revisions = limit

            while chunk_revisions == limit:
                pywikibot.output(u"\nDownloading: Title is: %s, total_revisions = %s, offset = %s" % (page.title(), total_revisions, offset))

                headers = {'User-Agent': 'PythonWikipediaBot/1.0'} # Needs to fool Wikipedia so it will give us the file
                params = urllib.urlencode({'title': 'Special:Export','pages': page.title(), 'action': 'submit', 'limit': limit, 'offset' : offset})
                req = urllib2.Request(url='http://en.wikipedia.org/w/index.php',data=params, headers=headers)
                fIN = urllib2.urlopen(req)
                filename = _output_arg + '/' + page.titleForFilename() + '.' + offset + '.xml'
                fOUT = open(filename, 'wb')
                fOUT.write(fIN.read())
                fOUT.close()
                fIN.close()
                pywikibot.output(u"\nDone writing. Filename is: %s" % filename)
                pywikibot.get_throttle()

                chunk_revisions = 0
                revisions = xmlreader.XmlDump(filename, allrevisions=True).parse()
                for e in revisions:
                    total_revisions += 1
                    chunk_revisions += 1

                pywikibot.output("Total revisions processed %d, Chunk revisions processed %d" % (total_revisions, chunk_revisions))
                if(chunk_revisions): pywikibot.output("Timestamp of the last revision: %s" % e.timestamp); offset = e.timestamp
                else: pywikibot.output("Error: Chunk revisions = 0"); break


        except pywikibot.NoPage:
            pywikibot.output(u"Page %s does not exist; skipping." % page.aslink())
            return
        except pywikibot.IsRedirectPage:
            pywikibot.output(u"Page %s is a redirect; skipping." % page.aslink())
            return


def main():
    global _output_arg
    _output_arg = '.'
    # This factory is responsible for processing command line arguments
    # that are also used by other scripts and that determine on which pages
    # to work on.
    genFactory = pagegenerators.GeneratorFactory()
    # The generator gives the pages that should be worked upon.
    gen = None
    # This temporary array is used to read the page title if one single
    # page to work on is specified by the arguments.
    pageTitleParts = []
    # If dry is True, doesn't do any real changes, but only show
    # what would have been changed.
    dry = False

    # Parse command line arguments
    for arg in pywikibot.handleArgs():
        if arg.startswith("-dry"):
            dry = True
        elif arg.startswith('-output') and len(arg) > 8:
            _output_arg = arg[8:]
        else:
            # check if a standard argument like
            # -start:XYZ or -ref:Asdf was given.
            if not genFactory.handleArg(arg):
                pageTitleParts.append(arg)

    if pageTitleParts != []:
        # We will only work on a single page.
        pageTitle = ' '.join(pageTitleParts)
        page = pywikibot.Page(pywikibot.getSite(), pageTitle)
        gen = iter([page])

    if not gen:
        gen = genFactory.getCombinedGenerator()
    if gen:
        # The preloading generator is responsible for downloading multiple
        # pages from the wiki simultaneously.
        gen = pagegenerators.PreloadingGenerator(gen)
        bot = BasicBot(gen, dry)
        bot.run()
    else:
        pywikibot.showHelp()

if __name__ == "__main__":
    try:
        main()
    finally:
        pywikibot.stopme()
