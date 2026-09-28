[4mOPAM[24m(1)                           Opam Manual                          [4mOPAM[24m(1)

[1mNAME[0m
       opam - source-based package management

[1mSYNOPSIS[0m
       [1mopam [22m[[4mCOMMAND[24m] …

[1mDESCRIPTION[0m
       Opam is a package manager. It uses the powerful mancoosi tools to
       handle dependencies, including support for version constraints,
       optional dependencies, and conflict management. The default
       configuration binds it to the official package repository for OCaml.

       It has support for different remote repositories such as HTTP, rsync,
       git, darcs and mercurial. Everything is installed within a local opam
       directory, that can include multiple installation prefixes with
       different sets of intalled packages.

       Use either [1mopam <command> --help [22mor [1mopam help <command> [22mfor more
       information on a specific command.

[1mCOMMANDS[0m
       [1madmin [22m[[4mOPTION[24m]…
           Tools for repository administrators

       [1mclean [22m[[4mOPTION[24m]…
           Cleans up opam caches

       [1mconfig [22m[[4mOPTION[24m]… [[4mCOMMAND[24m] [[4mARG[24m]…
           Display configuration options for packages.

       [1menv [22m[[4mOPTION[24m]…
           Prints appropriate shell variable assignments to stdout

       [1mexec [22m[[4mOPTION[24m]… [4mCOMMAND[24m [4m[ARG]...[24m…
           Executes a command in the proper opam environment

       [1mhelp [22m[[1m--man-format[22m=[4mFMT[24m] [[4mOPTION[24m]… [[4mTOPIC[24m]
           Display help about opam and opam commands.

       [1minit [22m[[4mOPTION[24m]… [[4mNAME[24m] [[4mADDRESS[24m]
           Initialize opam state, or set init options.

       [1minstall [22m[[4mOPTION[24m]… [[4mPACKAGES[24m]…
           Install a list of packages.

       [1mlint [22m[[4mOPTION[24m]… [[4mFILES[24m]…
           Checks and validate package description ('opam') files.

       [1mlist [22m[[4mOPTION[24m]… [[4mPATTERNS[24m]…
           Display the list of available packages.

       [1mlock [22m[[4mOPTION[24m]… [[4mPACKAGES[24m]…
           Create locked opam files to share build environments across hosts.

       [1moption [22m[[1m--global[22m] [[1m--no[22m] [[1m--yes[22m] [[4mOPTION[24m]… [[4mFIELD[(=|+=|-=)[VALUE]][24m]
           Global and switch configuration options settings

       [1mpin [22m[[4mOPTION[24m]… [[4mCOMMAND[24m] [[4mARG[24m]…
           Pin a given package to a specific version or source.

       [1mreinstall [22m[[4mOPTION[24m]… [[4mPACKAGES[24m]…
           Reinstall a list of packages.

       [1mremove [22m[[4mOPTION[24m]… [[4mPACKAGES[24m]…
           Remove a list of packages.

       [1mrepository [22m[[4mOPTION[24m]… [[4mCOMMAND[24m] [[4mARG[24m]…
           Manage opam repositories.

       [1mshow [22m[[4mOPTION[24m]… [[4mPACKAGES[24m]…
           Display information about specific packages.

       [1msource [22m[[4mOPTION[24m]… [4mPACKAGE[0m
           Get the source of an opam package.

       [1mswitch [22m[[4mOPTION[24m]… [[4mCOMMAND[24m] [[4mARG[24m]…
           Manage multiple installation prefixes.

       [1mupdate [22m[[4mOPTION[24m]… [[4mNAMES[24m]…
           Update the list of available packages.

       [1mupgrade [22m[[4mOPTION[24m]… [[4mPACKAGES[24m]…
           Upgrade the installed package to latest version.

       [1mvar [22m[[4mOPTION[24m]… [[4mVAR[=[VALUE]][24m]
           Display and update the value associated with a given variable

[1mCOMMAND ALIASES[0m
       [1minfo [22m[[4mOPTION[24m]… [[4mPACKAGES[24m]…
           An alias for [1mshow[22m.

       [1mremote [22m[[4mOPTION[24m]… [[4mCOMMAND[24m] [[4mARG[24m]…
           An alias for [1mrepository[22m.

       [1msearch [22m[[4mOPTION[24m]… [[4mPATTERNS[24m]…
           An alias for [1mlist --search[22m.

       [1muninstall [22m[[4mOPTION[24m]… [[4mPACKAGES[24m]…
           An alias for [1mremove[22m.

       [1munpin [22m[[4mOPTION[24m]… [[4mARG[24m]…
           An alias for [1mpin remove[22m.

[1mOPTIONS[0m
       [1m--no[0m
           Answer  no to all opam yes/no questions without prompting. See also
           [1m--confirm-level[22m. This is equivalent to setting [1m$OPAMNO [22mto "true".

       [1m-y[22m, [1m--yes[0m
           Answer yes to all opam yes/no questions without prompting. See also
           [1m--confirm-level[22m. This is equivalent to setting [1m$OPAMYES [22mto "true".

[1mCOMMON OPTIONS[0m
       These options are common to all commands.

       [1m--best-effort[0m
           Don't fail if all requested packages can't  be  installed:  try  to
           install as many as possible. Note that not all external solvers may
           support  this  option  (recent  versions of [4maspcud[24m or [4mmccs[24m should).
           This is equivalent to setting [1m$OPAMBESTEFFORT [22menvironment variable.

       [1m--cli[22m=[4mMAJOR.MINOR[24m (absent=[1m2.1[22m)
           Use the command-line interface syntax and semantics of [4mMAJOR.MINOR[24m.
           Intended for any persistent  use  of  opam  (scripts,  blog  posts,
           etc.),  any version of opam in the same MAJOR series will behave as
           for the specified MINOR release. The flag was not available in opam
           2.0, so to select the 2.0 CLI, set the [1mOPAMCLI [22menvironment variable
           to [4m2.0[24m instead of using this parameter.

       [1m--color[22m=[4mWHEN[0m
           Colorize the output. [4mWHEN[24m must be one of [1malways[22m, [1mnever [22mor [1mauto[22m.

       [1m--confirm-level[22m=[4mLEVEL[0m
           Confirmation  level,  [4mLEVEL[24m  must  be  one  of  [1mask[22m,  [1mno[22m,  [1myes   [22mor
           [1munsafe-yes[22m.  Can  be specified more than once. If [1m--yes [22mor [1m--no [22mare
           also given, the value of the last  [1m--confirm-level  [22mis  taken  into
           account. This is equivalent to setting  [1m$OPAMCONFIRMLEVEL[22m`.

       [1m--criteria[22m=[4mCRITERIA[0m
           Specify  user  [4mpreferences[24m  for  dependency  solving  for this run.
           Overrides both [1m$OPAMCRITERIA [22mand [1m$OPAMUPGRADECRITERIA[22m. For  details
           on  the supported language, and the external solvers available, see
           [4mhttp://opam.ocaml.org/doc/External_solvers.html[24m. A general guide to
           using     solver     preferences     can      be      found      at
           [4mhttp://www.dicosmo.org/Articles/usercriteria.pdf[24m.

       [1m--cudf[22m=[4mFILENAME[0m
           Debug  option:  Save  the  CUDF  requests  sent  to  the  solver to
           [4mFILENAME[24m-<n>.cudf.

       [1m--debug[0m
           Print debug message  to  stderr.  This  is  equivalent  to  setting
           [1m$OPAMDEBUG [22mto "true".

       [1m--debug-level[22m=[4mLEVEL[0m
           Like  [1m--debug[22m,  but allows specifying the debug level ([1m--debug [22msets
           it to 1). Equivalent to setting [1m$OPAMDEBUG [22mto a positive integer.

       [1m--git-version[0m
           Print the git version of  opam,  if  set  (i.e.  you  are  using  a
           development version), and exit.

       [1m--help[22m[=[4mFMT[24m] (default=[1mauto[22m)
           Show  this  help  in format [4mFMT[24m. The value [4mFMT[24m must be one of [1mauto[22m,
           [1mpager[22m, [1mgroff [22mor [1mplain[22m. With [1mauto[22m, the  format  is  [1mpager  [22mor  [1mplain[0m
           whenever the [1mTERM [22menv var is [1mdumb [22mor undefined.

       [1m--ignore-pin-depends[0m
           Ignore  extra  pins  required  by  packages that get pinned, either
           manually through [4mopam[24m [4mpin[24m or through  [4mopam[24m  [4minstall[24m  [4mDIR[24m.  This  is
           equivalent to setting [1mIGNOREPINDEPENDS=true[22m.

       [1m--json[22m=[4mFILENAME[0m
           Save  the  results  of the opam run in a computer-readable file. If
           the filename contains the character `%', it will be replaced by  an
           index  that  doesn't overwrite an existing file. Similar to setting
           the [1m$OPAMJSON [22mvariable.

       [1m--no-aspcud[0m
           Removed in [1m2.1[22m.

       [1m--no-auto-upgrade[0m
           When configuring or updating a repository that is  written  for  an
           earlier  opam  version  (1.2),  opam  internally converts it to the
           current  format.  This   disables   this   behaviour.   Note   that
           repositories should define their format version in a 'repo' file at
           their  root,  or they will be assumed to be in the older format. It
           is, in any case, preferable to upgrade  the  repositories  manually
           using [4mopam[24m [4madmin[24m [4mupgrade[24m [4m[--mirror[24m [4mURL][24m when possible.

       [1m--no-self-upgrade[0m
           Opam will replace itself with a newer binary found at [1mOPAMROOT/opam[0m
           if present. This disables this behaviour.

       [1m-q[22m, [1m--quiet[0m
           Disables [1m--verbose[22m.

       [1m--root[22m=[4mROOT[0m
           Use  [4mROOT[24m  as  the current root path. This is equivalent to setting
           [1m$OPAMROOT [22mto [4mROOT[24m.

       [1m--safe[22m, [1m--readonly[0m
           Make sure nothing  will  be  automatically  updated  or  rewritten.
           Useful  for calling from completion scripts, for example. Will fail
           whenever such an operation is needed  ;  also  avoids  waiting  for
           locks,  skips  interactive  questions  and overrides the [1m$OPAMDEBUG[0m
           variable. This is equivalent to set environment variable [1m$OPAMSAFE[22m.

       [1m--solver[22m=[4mCMD[0m
           Specify the CUDF solver to use for resolving  package  installation
           problems.  This is either a predefined solver (this version of opam
           supports           builtin-mccs+lp(),            builtin-mccs+glpk,
           builtin-dummy-z3-solver,   builtin-dummy-0install-solver,   aspcud,
           mccs, aspcud-old, packup), or a custom command that should  contain
           the  variables  %{input}%, %{output}%, %{criteria}%, and optionally
           %{timeout}%. This is equivalent to setting [1m$OPAMEXTERNALSOLVER[22m.

       [1m--strict[0m
           Fail whenever an error is  found  in  a  package  definition  or  a
           configuration   file.  The  default  is  to  continue  silently  if
           possible.

       [1m--switch[22m=[4mSWITCH[0m
           Use [4mSWITCH[24m as the current compiler switch. This  is  equivalent  to
           setting [1m$OPAMSWITCH [22mto [4mSWITCH[24m.

       [1m--use-internal-solver[0m
           Disable  any  external  solver,  and  use  the  built-in  one (this
           requires that opam has been compiled with a built-in solver).  This
           is equivalent to setting [1m$OPAMNOASPCUD [22mor [1m$OPAMUSEINTERNALSOLVER[22m.

       [1m-v[22m, [1m--verbose[0m
           Be  more verbose. One [1m-v [22mshows all package commands, repeat to also
           display commands called internally (e.g.  [4mtar[24m,  [4mcurl[24m,  [4mpatch[24m  etc.)
           Repeating [4mn[24m times is equivalent to setting [1m$OPAMVERBOSE [22mto "[4mn[24m".

       [1m--version[0m
           Show version information.

       [1m-w[22m, [1m--working-dir[0m
           Whenever   updating   packages   that   are   bound   to  a  local,
           version-controlled directory, update to the current  working  state
           of  their  source  instead  of the last committed state, or the ref
           they are pointing to. As source directory is copied as it is, if it
           isn't clean it may result on a opam build failure.This only affects
           packages explicitly listed on the command-line.It can also  be  set
           with [1m$OPAMWORKINGDIR[22m.

[1mENVIRONMENT[0m
       Opam  makes  use  of  the  environment  variables  listed here. Boolean
       variables should be set to "0", "no", "false" or the  empty  string  to
       disable, "1", "yes" or "true" to enable.

       [4mOPAMALLPARENS[24m surround all filters with parenthesis.

       [4mOPAMASSUMEDEPEXTS[24m see option `--assume-depexts'.

       [4mOPAMAUTOREMOVE[24m see remove option `--auto-remove'.

       [4mOPAMBESTEFFORT[24m see option `--best-effort'.

       [4mOPAMBESTEFFORTPREFIXCRITERIA[24m  sets the string that must be prepended to
       the criteria when the `--best-effort' option is set, and is expected to
       maximise the `opam-query' property in the solution.

       [4mOPAMBUILDDOC[24m Removed in [1m2.1[22m.

       [4mOPAMBUILDTEST[24m Removed in [1m2.1[22m.

       [4mOPAMCLI[24m see option `--cli'.

       [4mOPAMCOLOR[24m when set to [4malways[24m or [4mnever[24m, sets a  default  value  for  the
       `--color' option.

       [4mOPAMCONFIRMLEVEL[24m  see  option  `--confirm-level`.  [1mOPAMCONFIRMLEVEL [22mhas
       priority over [1mOPAMYES [22mand [1mOPAMNO[22m.

       [4mOPAMCRITERIA[24m specifies user [4mpreferences[24m  for  dependency  solving.  The
       default  value  depends  on  the solver version, use `config report' to
       know the current setting. See also option --criteria.

       [4mOPAMCUDFFILE[24m save the cudf graph to [4mfile[24m-actions-explicit.dot.

       [4mOPAMCUDFTRIM[24m controls the filtering of unrelated packages  during  CUDF
       preprocessing.

       [4mOPAMCURL[24m  can  be  used to select a given 'curl' program. See [4mOPAMFETCH[0m
       for more options.

       [4mOPAMDEBUG[24m see options `--debug' and `--debug-level'.

       [4mOPAMDEBUGSECTIONS[24m if set, limits debug messages to the  space-separated
       list  of  sections. Sections can optionally have a specific debug level
       (for  example,  [1mCLIENT:2  [22mor  [1mCLIENT   CUDF:2[22m),   but   otherwise   use
       `--debug-level'.

       [4mOPAMDIGDEPTH[24m  defines  how  aggressive  the lookup for conflicts during
       CUDF preprocessing is.

       [4mOPAMDOWNLOADJOBS[24m sets the maximum number of simultaneous downloads.

       [4mOPAMDROPWORKINGDIR[24m   overrides   packages   previously   updated   with
       [1m--working-dir  [22mon  update.  Without  this variable set, opam would keep
       them unchanged unless explicitly named on the command-line.

       [4mOPAMDRYRUN[24m see option `--dry-run'.

       [4mOPAMEDITOR[24m sets the editor to use  for  opam  file  editing,  overrides
       [4m$EDITOR[24m and [4m$VISUAL[24m.

       [4mOPAMERRLOGLEN[24m  sets  the number of log lines printed when a sub-process
       fails. 0 to print all.

       [4mOPAMEXTERNALSOLVER[24m see option `--solver'.

       [4mOPAMFAKE[24m see option `--fake'.

       [4mOPAMFETCH[24m specifies how to download files: either `wget', `curl'  or  a
       custom   command   where   variables   [1m%{url}%[22m,   [1m%{out}%[22m,   [1m%{retry}%[22m,
       [1m%{compress}%  [22mand  [1m%{checksum}%  [22mwill  be   replaced.   Overrides   the
       'download-command' value from the main config file.

       [4mOPAMFIXUPCRITERIA[24m same as [4mOPAMUPGRADECRITERIA[24m, but specific to fixup.

       [4mOPAMIGNORECONSTRAINTS[24m see install option `--ignore-constraints-on'.

       [4mOPAMIGNOREPINDEPENDS[24m see option `--ignore-pin-depends'.

       [4mOPAMINPLACEBUILD[24m see option `--inplace-build'.

       [4mOPAMJOBS[24m sets the maximum number of parallel workers to run.

       [4mOPAMJSON[24m  log json output to the given file (use character `%' to index
       the files).

       [4mOPAMKEEPBUILDDIR[24m see install option `--keep-build-dir'.

       [4mOPAMKEEPLOGS[24m tells opam to not remove some temporary command  logs  and
       some  backups. This skips some finalisers and may also help to get more
       reliable backtraces.

       [4mOPAMLOCKED[24m combination of `--locked' and `--lock-suffix' options.

       [4mOPAMLOGS[24m [4mlogdir[24m sets log directory, default is a temporary directory in
       /tmp

       [4mOPAMMAKECMD[24m set the system make command to use.

       [4mOPAMMERGEOUT[24m merge process outputs, stderr on stdout.

       [4mOPAMNO[24m answer  no  to  any  question  asked,  see  options  `--no`  and
       `--confirm-level`.  [1mOPAMNO  [22mis  ignored  if  either [1mOPAMCONFIRMLEVEL [22mor
       [1mOPAMYES [22mis set.

       [4mOPAMNOAGGREGATE[24m with `opam admin check', don't aggregate packages.

       [4mOPAMNOASPCUD[24m Deprecated.

       [4mOPAMNOAUTOUPGRADE[24m disables automatic internal upgrade  of  repositories
       in an earlier format to the current one, on 'update' or 'init'.

       [4mOPAMNOCHECKSUMS[24m enables option --no-checksums when available.

       [4mOPAMNODEPEXTS[24m   disables   system  dependencies  handling,  see  option
       `--no-depexts'.

       [4mOPAMNOENVNOTICE[24m Internal.

       [4mOPAMNOSELFUPGRADE[24m see option `--no-self-upgrade'

       [4mOPAMPINKINDAUTO[24m sets whether version control systems should be detected
       when pinning to a local path. Enabled by default since 1.3.0.

       [4mOPAMPRECISETRACKING[24m fine grain tracking of directories.

       [4mOPAMPREPRO[24m set this  to  false  to  disable  CUDF  preprocessing.  Less
       efficient, but might help debugging solver issue.

       [4mOPAMREQUIRECHECKSUMS[24m    Enables   option   `--require-checksums'   when
       available (e.g. for `opam install').

       [4mOPAMRETRIES[24m sets the number of tries before failing downloads.

       [4mOPAMREUSEBUILDDIR[24m see option `--reuse-build-dir'.

       [4mOPAMROOT[24m see option `--root'. This is automatically set  by  `opam  env
       --root=DIR --set-root'.

       [4mOPAMROOTISOK[24m don't complain when running as root.

       [4mOPAMSAFE[24m see option `--safe'.

       [4mOPAMSHOW[24m see option `--show'.

       [4mOPAMSKIPUPDATE[24m see option `--skip-updates'.

       [4mOPAMSKIPVERSIONCHECKS[24m   bypasses   some  version  checks.  Unsafe,  for
       compatibility testing only.

       [4mOPAMSOLVERALLOWSUBOPTIMAL[24m (default `true') allows some solvers to still
       return a solution when they reach timeout; while the  solution  remains
       assured  to  be  consistent, there is no guarantee in this case that it
       fits the expected optimisation criteria. If `true',  opam  willcontinue
       with  a  warning,  if `false' a timeout is an error. Currently only the
       builtin-z3 backend handles this degraded case.

       [4mOPAMSOLVERTIMEOUT[24m change the time allowance of the solver.  Default  is
       60.0,  set  to  0  for unlimited. Note that all solvers may not support
       this option.

       [4mOPAMSTATS[24m display stats at the end of command.

       [4mOPAMSTATUSLINE[24m display a dynamic status line showing  what's  currently
       going on on the terminal. (one of one of [1malways[22m, [1mnever [22mor [1mauto[22m)

       [4mOPAMSTRICT[24m fail on inconsistencies (file reading, switch import, etc.).

       [4mOPAMSWITCH[24m  see  option  `--switch'.  Automatically  set  by  `opam env
       --switch=SWITCH --set-switch'.

       [4mOPAMUNLOCKBASE[24m see install option `--unlock-base'.

       [4mOPAMUPGRADECRITERIA[24m specifies user [4mpreferences[24m for  dependency  solving
       when  performing an upgrade. Overrides [4mOPAMCRITERIA[24m in upgrades if both
       are set. See also option --criteria.

       [4mOPAMUSEINTERNALSOLVER[24m see option `--use-internal-solver'.

       [4mOPAMUSEOPENSSL[24m force openssl use for hash computing.

       [4mOPAMUTF8[24m use UTF8 characters in output (one of one of [1malways[22m, [1mnever  [22mor
       [1mauto[22m). By default `auto', which is determined from the locale).

       [4mOPAMUTF8MSGS[24m  use  extended  UTF8 characters (camels) in opam messages.
       Implies [4mOPAMUTF8[24m. This is set by default on OSX only.

       [4mOPAMVALIDATIONHOOK[24m if set, uses the `%{hook%}' command to  validate  an
       opam repository update.

       [4mOPAMVERBOSE[24m see option `--verbose'.

       [4mOPAMVERSIONLAGPOWER[24m do not use.

       [4mOPAMWITHDOC[24m see install option `--with-doc'.

       [4mOPAMWITHTEST[24m see install option `--with-test.

       [4mOPAMWORKINGDIR[24m see option `--working-dir'.

       [4mOPAMYES[24m  see  options  `--yes'  and  `--confirm-level`. [1mOPAMYES [22mhas has
       priority over [1mOPAMNO [22mand is ignored if [1mOPAMCONFIRMLEVEL [22mis set.

       [4mOPAMVAR_var[24m  overrides  the  contents  of   the   variable   [4mvar[24m   when
       substituting `%{var}%` strings in `opam` files.

       [4mOPAMVAR_package_var[24m  overrides the contents of the variable [4mpackage:var[0m
       when substituting `%{package:var}%` strings in `opam` files.

[1mCLI VERSION[0m
       All scripts and programmatic invocations of opam should use `--cli'  in
       order  to  ensure that they work seamlessly with future versions of the
       opam client.  Additionally,  blog  posts  or  other  documentation  can
       benefit, as it prevents information from becoming stale.

       Although  opam  only supports roots ([4m~/.opam/[24m) for the current version,
       it does provide backwards compatibility for its command-line interface.

       Since CLI version support was only added in opam 2.1,  use  [4mOPAMCLI[24m  to
       select  2.0  support (as opam 2.0 will just ignore it), and `--cli=2.1'
       for 2.1 (or later) versions, since an environment variable  controlling
       the  parsing of syntax is brittle. To this end, opam displays a warning
       if [4mOPAMCLI[24m specifies a valid  version  other  than  2.0,  and  also  if
       `--cli=2.0' is specified.

       The command-line version is selected by using the `--cli' option or the
       [4mOPAMCLI[24m  environment  variable. `--cli' may be specified morethan once,
       where the last instance takes precedence. [4mOPAMCLI[24m is only inspected  if
       `--cli' is not given.

[1mEXIT STATUS[0m
       As an exception to the following, the `exec' command returns 127 if the
       command  was  not found or couldn't be executed, and the command's exit
       value otherwise.

       0   Success, or true for boolean queries.

       1   False. Returned when a boolean return value is expected, e.g.  when
           running with [1m--check[22m, or for queries like [1mopam lint[22m.

       2   Bad  command-line  arguments, or command-line arguments pointing to
           an invalid context (e.g. file not following the expected format).

       5   Not found. You requested something (package,  version,  repository,
           etc.) that couldn't be found.

       10  Aborted. The operation required confirmation, which wasn't given.

       15  Could not acquire the locks required for the operation.

       20  There  is  no  solution  to the user request. This can be caused by
           asking to install two incompatible packages, for example.

       30  Error  in  package  definition,  or  other  metadata  files.  Using
           [1m--strict [22mraises this error more often.

       31  Package  script  error.  Some package operations were unsuccessful.
           This may be an error in the packages  or  an  incompatibility  with
           your system. This can be a partial error.

       40  Sync error. Could not fetch some remotes from the network. This can
           be a partial error.

       50  Configuration  error.  Opam  or  system configuration doesn't allow
           operation, and needs fixing.

       60  Solver failure. The solver failed to return a sound answer. It  can
           be  due  to  a  broken  external  solver,  or  an  error  in solver
           configuration.

       99  Internal error. Something went wrong, likely due to a bug  in  opam
           itself.

       130 User  interrupt.  SIGINT  was  received,  generally due to the user
           pressing Ctrl-C.

[1mFURTHER DOCUMENTATION[0m
       See https://opam.ocaml.org/doc.

[1mAUTHORS[0m
       Vincent Bernardoff <vb@luminar.eu.org>
       Raja Boujbel <raja.boujbel@ocamlpro.com>
       Roberto Di Cosmo <roberto@dicosmo.org>
       Thomas Gazagnaire <thomas@gazagnaire.org>
       Louis Gesbert <louis.gesbert@ocamlpro.com>
       Fabrice Le Fessant <Fabrice.Le_fessant@inria.fr>
       Anil Madhavapeddy <anil@recoil.org>
       Guillem Rieu <guillem.rieu@ocamlpro.com>
       Ralf Treinen <ralf.treinen@pps.jussieu.fr>
       Frederic Tuong <tuong@users.gforge.inria.fr>

[1mBUGS[0m
       Check bug reports at https://github.com/ocaml/opam/issues.

Opam 2.1.5                                                             [4mOPAM[24m(1)
