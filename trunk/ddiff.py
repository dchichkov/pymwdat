#!/usr/bin/python
# -*- coding: utf-8  -*-

"""
Dumb Diff: Diff algorithm tailored specifiably for Wikipedia articles (v. detection)
  While ugly, it's efficient and works well on Wiki articles. It is:
  * Fast;
  * Produces human readable results;
  * Keeps tokens order;
  * Returns edit position;
  * Detects duplications.

Algorithm:
 1. cut same head, same tail
 2. put A into the OrderedDict
 3. remove B from the OrderedDict
 4. dump nonzero result
 
 Typical usage (two stages):
  al = e.text.splitlines()
  bl = e.text.splitlines()
  (d, dposl) = ddiff.ddiff_v3(al, bl)    # calculate ddiff for lines
  
  a = []; b = [];  ilA = 0; ilR = 0;     # merge and tokenize
  for line, v in d.items():
      if(v > 0): b.extend(line.split()); ilA += 1
      elif(v < 0): a.extend(line.split()); llB += 1

  (d, dpost) = ddiff.ddiff(a, b);    # calculate ddiff for tokens
  itA = 0; itR = 0;
  for token, v in d.items():
      if(v > 0): itA += 1            # +token
      elif(v < 0): itR += 1          # -token



In my research I've found that there is a need for a diff algorithm
designed specifically to diff consecutive revisions of a single
Wikipedia article for v. detection. More specifically algorithm/
algorithm implementation with the following properties:

* Fast. (Order of 5*10^3 diffs / second on a regular desktop for a
  regular article; entire en. Wikipedia history/day);
* Accuracy and completeness of the generated diff can be sacrificed for speed.
* Differences that it produces are human-readable;
* Ignores / detects copy-edits. (see http://en.wikipedia.org/wiki/Copy_editing);
* Keeps tokens order (trigrams should be left mostly unchanged);
* Detects and returns approximate edit position in the article;
* Detects insertions and removal of duplicate tokens;
* Size of the generated differences could be limited.

I think I was able to address these requirements with a very simple
algorithm which comes down to adding/removing revisions texts to/from
an ordered dictionary (map) in two stages - first for lines, next for
tokens. I'm going to illustrate it on the following example.

Revision 1:
 HEAD.
 The quick /**/ brown fox jumps over the lazy dog.
 TAIL.

Revision 2:
 HEAD.
 The quick brown fox FUN FUN FUN jumps over the /**/ lazy dog.
 TAIL.

Step 1. Split into lines, remove matching head and tail (& store
approximate edit position). Result:
 Lines from R1: The quick /**/ brown fox jumps over the lazy dog.
 Lines from R2: The quick brown fox FUN FUN FUN jumps over the /**/ lazy dog.

Step 2: Create empty ordered dictionary D1 mapping the text into the
number of occurrences.

Step 3. Add lines from R1 into the D1. Result (D1):
 The quick /**/ brown fox jumps over the lazy dog.  --->  1

Step 4. Add lines from R2 into the D1 with the opposite sign. Result (D1):
 The quick /**/ brown fox jumps over the lazy dog.  --->  1
 The quick brown fox FUN FUN FUN jumps over the /**/ lazy dog.   --->  -1

Step 5. Take all keys (lines) with the positive values from D1, split
into tokens, add to the list T1. Result (T1):
 [The, quick, /**/, brown, fox, jumps, over, the, lazy, dog.]

Step 6. Take all keys (lines) with the negative values from D1, split
into tokens, add to the list T2. Result (T2):
 [The, quick, brown, fox, FUN, FUN, FUN, jumps, over, the, /**/, lazy, dog.]

Step 7. Create empty ordered dictionary D2 mapping tokens into the
number of occurrences.

Step 8. Add tokens  from T2 into the D2. Result (D2):
  [The : 1, quick : 1, brown : 1, fox : 1, FUN : 3, jumps : 1, over :1, 
  the : 1, /**/ : 1, lazy : 1, dog. : 1]

Step 9. Add tokens from T1 into the D2 with the opposite sign. Result (D2):
  [The : 0, quick : 0, brown : 0, fox : 0, FUN : 3, jumps : 0, over :0, 
  the : 0, /**/ : 0, lazy : 0, dog. : 0]

Step 10. Take all keys with nonzero values from D2, that's your diff result:
  +FUN

As you can see, this algorithm is fairly simple, the only tricky parts
are the use of ordered dictionary and doing the diff in two stages -
first for lines and next for tokens. Advantages of doing the diff in
two stages are 1) speed 2) resulting tokens order remains more or less
the same.

I've also found that this algorithm resists/detects copy-edits well;
resulting diffs are remarkably human readable (e.g. better or same as
ndiff); for typical Wikipedia revisions it is several orders of
magnitude faster than basic Ratcliff-Obershelp algorithm/gestalt
approach. With this algorithm it is also fairly easy to limit the size
of the produced diff, detect repeating tokens and get an approximate
position of the edit.

"""


__version__ = "0.0.0a1"

__license__ = """
Copyright (C) 2010 Dmitry Chichkov.

This program is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public License
as published by the Free Software Foundation; either version 2
of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA
"""

from collections import OrderedDict

def ddiff(a, b):
    ahi = len(a); bhi = len(b)          # find last matching 
    while ahi > 0 and bhi > 0:
        ahi -= 1; bhi -= 1;
        if(a[ahi] != b[bhi]): ahi += 1; bhi += 1; break
    
    d = OrderedDict()
    ait = iter(a); bit = iter(b); lo = hi = min(ahi, bhi) 
    for i in xrange(hi):                     
        at = ait.next(); bt = bit.next()
        if(at == bt): continue
        if(lo == hi): lo = i 
        d[at] = d.setdefault(at, 0) - 1
        d[bt] = d.setdefault(bt, 0) + 1
        
    for i in xrange(hi, ahi):
        at = ait.next();        
        d[at] = d.setdefault(at, 0) - 1
        
    for i in xrange(hi, bhi):
        bt = bit.next()
        d[bt] = d.setdefault(bt, 0) + 1
        
    return (d, (lo, ahi, bhi))



if __name__ == "__main__":
    import unittest
    from difflib import SequenceMatcher, ndiff, Differ

    def ddiff_v1(a, b):
        cruncher = SequenceMatcher(None, a, b)
        d = OrderedDict()
        for tag, alo, ahi, blo, bhi in cruncher.get_opcodes():
            if(tag == 'insert' or tag == 'replace'): 
                for t in b[blo:bhi]: 
                    d[t] = d.setdefault(t, 0) + 1
            if(tag == 'delete' or tag == 'replace'):
                for t in a[alo:ahi]:
                    d[t] = d.setdefault(t, 0) - 1                
        for t, v in d.items():
            if(v > 0): yield '+' + t
            elif(v < 0): yield '-' + t
    
    
    def ddiff_v2(a, b):
        (d, dpos) = ddiff(a, b)
        for t, v in d.items():
            if(v > 0): yield '+' + t
            elif(v < 0): yield '-' + t

    a = "HEAD. The quick /**/ brown fox jumps over the lazy dog. TAIL".split() 
    b = "HEAD. The quick brown fox FUN FUN FUN jumps over the /**/ lazy dog. TAIL".split()
    print "a = '%s'" % a
    print "b = '%s'" % b

    class DefaultTests(unittest.TestCase):
        def test_ddiff(self):
            print "\n"
            d = ddiff(a, b)
            c = (OrderedDict([('/**/', 0), ('brown', 0), ('fox', 0), ('FUN', 3), 
                              ('jumps', 0), ('over', 0), ('the', 0)]), (3, 9, 12))
            print d
            self.assertEqual(d, c)
            
        def test_ddiff_v1(self):
            """verify that ddiff_v1 works"""
            print "\n"
            for d in ddiff_v1(a, b): print d
            self.assertEqual(d, "+FUN")

        def test_ddiff_v2(self):
            """verify that ddiff_v2 works"""
            print "\n"
            for d in ddiff_v2(a, b): print d
            self.assertEqual(d, "+FUN")

        def test_ndiff(self):
            """results from the ndiff"""
            print "\n"
            for d in ndiff(a, b): print d

    suite = unittest.TestLoader().loadTestsFromTestCase(DefaultTests)
    unittest.TextTestRunner(verbosity=2).run(suite)
