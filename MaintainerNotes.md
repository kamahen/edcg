# Maintainer Notes

This document contains miscellaneous notes for maintaining the package.

# Workflow

(See also https://www.swi-prolog.org/howto/Pack.txt)

If you change the github location, you'll need to send a message to
Jan Wielemaker jan@swi-prolog.org to update the URL pattern to
`https://github.com/<user>/edcg/*` or similar.

  * `git clone https://github.com/kamahen/edcg.git`
    * Only needed once.
  * Verify the remote: `git remote -v`
  * `find t -name '*.pl' | xargs -L1 swipl -g run_tests -g halt`
  * Update version in files:
    * `History.md`
    * `pack.pl`
  * `git commit -m'...' -a`
  * `git tag v0.9.x`
  * `git push`
  * `git push --tags`
  * Verify the new release is in `https://github.com/kamahen/edcg/releases`
  * `swipl`
    * `pack_remove(edcg).`
    * `pack_install('https://github.com/kamahen/edcg/archive/v0.9.x.zip').`
    * `pack_remove(edcg).`
    * `pack_install(edcg). % Should get the new version`
  * Wait an hour, verify https://www.swi-prolog.org/pack/list?p=edcg

# Discussions

Discussion about modules and multi-file directives in edcg.pl:
https://swi-prolog.discourse.group/t/using-consult-in-a-directive-to-load-source-code-it-puzzles-me/2081

Note that logtalk has its own port, which avoids the `edcg:pred_info` multifile predicates.
