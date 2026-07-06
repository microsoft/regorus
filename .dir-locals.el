;;; Directory Local Variables            -*- no-byte-compile: t; -*-
;;; For more information see (info "(emacs) Directory Variables")

;; Regorus is a cargo-verus project (package.metadata.verus.verify = true), so
;; verus-mode.el runs `cargo verus verify' rather than the raw `verus' binary.
;; The cargo-verus path ignores `package.metadata.verus.ide.extra_args' and
;; instead reads `verus-cargo-verus-arguments'. We set it here so that Verus is
;; invoked with the `verus' Cargo feature enabled.
;;
;; Everything before `--' is passed to cargo-verus; everything after `--' is
;; forwarded to the Verus binary. The `--' is required by verus-mode.el.
((verus-mode . ((verus-cargo-verus-arguments . ("--features" "verus" "--")))))
