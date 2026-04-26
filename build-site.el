;;; build-site.el --- Export the SSFT site from Org. -*- lexical-binding: t; -*-

(require 'ox-html)

(setq org-html-doctype "html5"
      org-html-html5-fancy t
      org-html-validation-link nil
      org-html-postamble nil
      org-html-head "<link rel=\"stylesheet\" href=\"style.css\" />"
      org-html-head-include-default-style nil
      org-html-head-include-scripts nil
      org-html-htmlize-output-type 'css
      org-html-metadata-timestamp-format "Generated from Org source"
      org-export-with-smart-quotes t
      org-export-with-broken-links 'mark
      org-html-divs '((preamble "header" "preamble")
                      (content "main" "content")
                      (postamble "footer" "postamble")))

(let* ((root (file-name-directory (or load-file-name buffer-file-name default-directory)))
       (source (expand-file-name "index.org" root))
       (target (expand-file-name "index.html" root)))
  (with-current-buffer (find-file-noselect source)
    (setq-local org-export-use-babel nil)
    (org-export-to-file 'html target)))
