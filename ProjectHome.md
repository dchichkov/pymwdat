Somewhat cleaned up version of the MediaWiki Dump Analysis code from the wredese project.  I must warn you, that I haven't really spend much time cleaning up that code. And when I was writing the original version, I was concentrating on a get-results-quick-and-dirty approach, rather than on designing beautiful and reusable code.

Requirements:
  * Python 2.6+, Linux;
  * OrderedDict (available in Python 2.7 or http://pypi.python.org/pypi/ordereddict/)
  * 7-Zip (command line 7za, **sudo apt-get install p7zip-full**)

Input Alternatives:
  * Wikipedia history dump (e.g. enwiki-20100130-pages-meta-history.xml.7z);
  * Wikipedia page(s) name / category;
  * Wikipedia page(s) history (.xml/.7z/.bz2/.gz).

Input Processing:
  * Detects reverts, reverted edits, revert wars, self-reverts;
  * Filtering, labeled revisions data sets management, etc;
  * Calculates users/page counters, revert rates, page diffs, etc (~1 week/C2Duo/Full English Wikipedia dump).

See more details in the project's http://code.google.com/p/pymwdat/source/browse/trunk/README file.