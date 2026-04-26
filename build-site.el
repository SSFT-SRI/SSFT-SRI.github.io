;;; build-site.el --- Export the SSFT site from Org. -*- lexical-binding: t; -*-

(require 'cl-lib)
(require 'subr-x)
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

(cl-defstruct ssft-event date start end title speaker type location description)

(defun ssft-keyword (name default)
  (save-excursion
    (goto-char (point-min))
    (let ((case-fold-search t))
      (if (re-search-forward
           (format "^%s%s:[ \t]*\\(.*\\)$"
                   (regexp-quote "#+")
                   (regexp-quote name))
           nil t)
          (string-trim (match-string-no-properties 1))
        default))))

(defun ssft-time-to-minutes (time)
  (unless (string-match "\\`\\([0-9][0-9]?\\):\\([0-9][0-9]\\)\\'" time)
    (error "Invalid time: %s" time))
  (+ (* 60 (string-to-number (match-string 1 time)))
     (string-to-number (match-string 2 time))))

(defun ssft-minutes-to-time (minutes)
  (let* ((hour (/ minutes 60))
         (minute (% minutes 60))
         (period (if (< hour 12) "AM" "PM"))
         (display-hour (% hour 12)))
    (when (= display-hour 0)
      (setq display-hour 12))
    (format "%d:%02d %s" display-hour minute period)))

(defun ssft-date-to-time (date)
  (pcase-let ((`(,year ,month ,day)
               (mapcar #'string-to-number (split-string date "-"))))
    (encode-time 0 0 12 day month year)))

(defun ssft-date-range (start end)
  (let ((current (ssft-date-to-time start))
        (last (ssft-date-to-time end))
        dates)
    (while (not (time-less-p last current))
      (push (format-time-string "%Y-%m-%d" current) dates)
      (setq current (time-add current (days-to-time 1))))
    (nreverse dates)))

(defun ssft-event-duration (type duration)
  (cond
   ((and duration (not (string-empty-p duration)))
    (string-to-number duration))
   ((member (downcase type) '("lecture" "invited"))
    90)
   (t
    30)))

(defun ssft-class-name (value)
  (let ((class (replace-regexp-in-string
                "[^a-z0-9]+" "-"
                (downcase (or value "other")))))
    (string-trim class "-+" "-+")))

(defun ssft-trim-leading-blank-lines ()
  (goto-char (point-min))
  (while (and (not (eobp))
              (looking-at-p "[ \t]*$"))
    (forward-line 1))
  (delete-region (point-min) (point)))

(defun ssft-event-description-html ()
  (save-excursion
    (org-back-to-heading t)
    (let* ((element (org-element-at-point))
           (begin (org-element-property :contents-begin element))
           (end (org-element-property :contents-end element)))
      (when (and begin end)
        (let ((raw (buffer-substring-no-properties begin end)))
          (with-temp-buffer
            (insert raw)
            (org-mode)
            (ssft-trim-leading-blank-lines)
            (goto-char (point-min))
            (when (looking-at-p "[ \t]*:PROPERTIES:[ \t]*$")
              (let ((drawer-start (line-beginning-position)))
                (when (re-search-forward "^[ \t]*:END:[ \t]*$" nil t)
                  (delete-region drawer-start (line-end-position)))))
            (ssft-trim-leading-blank-lines)
            (goto-char (point-min))
            (when (re-search-forward "^\\*+ " nil t)
              (delete-region (match-beginning 0) (point-max)))
            (let ((text (string-trim (buffer-string))))
              (unless (string-empty-p text)
                (org-export-string-as text 'html t)))))))))

(defun ssft-cell (row header)
  (or (cdr (assoc header row)) ""))

(defun ssft-normalize-cell (value)
  (string-trim (or value "")))

(defun ssft-org-fragment-to-html (text)
  (let ((text (string-trim (or text ""))))
    (unless (string-empty-p text)
      (org-export-string-as text 'html t))))

(defun ssft-table-to-alists (table)
  (let* ((rows (cl-remove-if
                (lambda (row)
                  (or (eq row 'hline)
                      (eq (car-safe row) 'hline)))
                table))
         (headers (mapcar (lambda (cell)
                            (upcase (ssft-normalize-cell cell)))
                          (car rows))))
    (mapcar (lambda (row)
              (cl-mapcar (lambda (header cell)
                           (cons header (ssft-normalize-cell cell)))
                         headers row))
            (cdr rows))))

(defun ssft-note-html-from-headline ()
  (save-excursion
    (org-back-to-heading t)
    (let* ((element (org-element-at-point))
           (begin (org-element-property :contents-begin element))
           (end (org-element-property :contents-end element)))
      (when (and begin end)
        (let ((raw (buffer-substring-no-properties begin end)))
          (with-temp-buffer
            (insert raw)
            (org-mode)
            (ssft-trim-leading-blank-lines)
            (let ((text (string-trim (buffer-string))))
              (unless (string-empty-p text)
                (ssft-org-fragment-to-html text)))))))))

(defun ssft-collect-schedule-notes ()
  (let ((notes (make-hash-table :test 'equal)))
    (org-map-entries
     (lambda ()
       (let ((id (org-entry-get nil "CUSTOM_ID")))
         (when id
           (puthash id (ssft-note-html-from-headline) notes))))
    nil 'file)
    notes))

(defun ssft-row-description-html (row notes)
  (let (parts)
    (when-let ((details-html (ssft-org-fragment-to-html
                              (ssft-cell row "DETAILS"))))
      (push details-html parts))
    (let ((note-id (ssft-cell row "NOTE_ID")))
      (when (not (string-empty-p note-id))
        (when-let ((note-html (gethash note-id notes)))
          (push note-html parts))))
    (unless (null parts)
      (mapconcat #'identity (nreverse parts) ""))))

(defun ssft-collect-schedule-table-events ()
  (let ((notes (ssft-collect-schedule-notes))
        events
        table-found)
    (org-element-map (org-element-parse-buffer) 'table
      (lambda (table)
        (when (let ((headline (org-element-lineage table '(headline) t)))
                (and headline
                     (string= (org-element-property :raw-value headline)
                              "Schedule table")))
          (setq table-found t)
          (let ((rows (ssft-table-to-alists
                       (org-table-to-lisp
                        (buffer-substring-no-properties
                         (org-element-property :begin table)
                         (org-element-property :end table))))))
            (dolist (row rows)
              (let* ((date (ssft-cell row "DATE"))
                     (start (ssft-cell row "START"))
                     (type (or (ssft-cell row "TYPE") "other"))
                     (duration (ssft-cell row "DURATION")))
                (when (and (not (string-empty-p date))
                           (not (string-empty-p start)))
                  (let* ((start-minutes (ssft-time-to-minutes start))
                         (end-minutes (+ start-minutes
                                         (ssft-event-duration type duration))))
                    (push (make-ssft-event
                           :date date
                           :start start-minutes
                           :end end-minutes
                           :title (ssft-cell row "TITLE")
                           :speaker (ssft-cell row "SPEAKER")
                           :type type
                           :location (ssft-cell row "LOCATION")
                           :description (ssft-row-description-html row notes))
                          events))))))))
      nil nil nil t)
    (when table-found
      (sort events #'ssft-event<))))

(defun ssft-event< (a b)
  (or (string< (ssft-event-date a) (ssft-event-date b))
      (and (string= (ssft-event-date a) (ssft-event-date b))
           (< (ssft-event-start a) (ssft-event-start b)))))

(defun ssft-collect-schedule-events ()
  (or (ssft-collect-schedule-table-events)
      (let (events)
        (org-map-entries
         (lambda ()
           (let ((start (org-entry-get nil "START")))
             (when start
               (let* ((date (org-entry-get nil "DATE" t))
                      (type (or (org-entry-get nil "TYPE" t) "other"))
                      (duration (org-entry-get nil "DURATION" t))
                      (start-minutes (ssft-time-to-minutes start))
                      (end-minutes (+ start-minutes
                                      (ssft-event-duration type duration)))
                      (title (nth 4 (org-heading-components))))
                 (push (make-ssft-event
                        :date date
                        :start start-minutes
                        :end end-minutes
                        :title title
                        :speaker (org-entry-get nil "SPEAKER" t)
                        :type type
                        :location (org-entry-get nil "LOCATION" t)
                        :description (ssft-event-description-html))
                       events)))))
         nil 'file)
        (sort events #'ssft-event<))))

(defun ssft-index-events (events slot-minutes)
  (let ((starts (make-hash-table :test 'equal))
        (covered (make-hash-table :test 'equal)))
    (dolist (event events)
      (push event (gethash (list (ssft-event-date event)
                                 (ssft-event-start event))
                           starts))
      (let ((slot (+ (ssft-event-start event) slot-minutes)))
        (while (< slot (ssft-event-end event))
          (puthash (list (ssft-event-date event) slot) t covered)
          (setq slot (+ slot slot-minutes)))))
    (list starts covered)))

(defun ssft-render-schedule-item (event)
  (let ((title (org-html-encode-plain-text (ssft-event-title event)))
        (speaker (ssft-event-speaker event))
        (location (ssft-event-location event))
        (description (ssft-event-description event)))
    (concat
     "<div class=\"schedule-item\">"
     "<div class=\"schedule-event-title\">" title "</div>"
     (when (and speaker (not (string-empty-p speaker)))
       (format "<div class=\"schedule-speaker\">%s</div>"
               (org-html-encode-plain-text speaker)))
     (when (and location (not (string-empty-p location)))
       (format "<div class=\"schedule-location\">%s</div>"
               (org-html-encode-plain-text location)))
     (when (and description (not (string-empty-p description)))
       (format "<div class=\"schedule-description\">%s</div>"
               description))
     "</div>")))

(defun ssft-render-event-cell (events slot-minutes)
  (let* ((events (sort (copy-sequence events)
                       (lambda (a b)
                         (< (ssft-event-end a) (ssft-event-end b)))))
         (start (ssft-event-start (car events)))
         (end (apply #'max (mapcar #'ssft-event-end events)))
         (rowspan (max 1 (/ (- end start) slot-minutes)))
         (type (if (= (length events) 1)
                   (ssft-event-type (car events))
                 "multiple")))
    (format "<td class=\"schedule-event schedule-type-%s\" rowspan=\"%d\">%s</td>"
            (ssft-class-name type)
            rowspan
            (mapconcat #'ssft-render-schedule-item events ""))))

(defun ssft-day-heading (date)
  (let ((time (ssft-date-to-time date)))
    (format "%s<br /><span>%s</span>"
            (format-time-string "%A" time)
            (string-trim (format-time-string "%B %e" time)))))

(defun ssft-render-schedule-html ()
  (let* ((start-date (ssft-keyword "SSFT_SCHEDULE_START_DATE" "2026-05-23"))
         (end-date (ssft-keyword "SSFT_SCHEDULE_END_DATE" "2026-05-29"))
         (day-start (ssft-time-to-minutes
                     (ssft-keyword "SSFT_SCHEDULE_DAY_START" "08:00")))
         (day-end (ssft-time-to-minutes
                   (ssft-keyword "SSFT_SCHEDULE_DAY_END" "18:30")))
         (slot-minutes (string-to-number
                        (ssft-keyword "SSFT_SCHEDULE_SLOT_MINUTES" "30")))
         (dates (ssft-date-range start-date end-date))
         (events (ssft-collect-schedule-events))
         (indexes (ssft-index-events events slot-minutes))
         (starts (car indexes))
         (covered (cadr indexes))
         (slots)
         (rows))
    (let ((slot day-start))
      (while (< slot day-end)
        (push slot slots)
        (setq slot (+ slot slot-minutes))))
    (setq slots (nreverse slots))
    (push "<div class=\"schedule-scroll\"><table class=\"schedule-table\">" rows)
    (push "<thead><tr><th class=\"schedule-time-heading\">Time</th>" rows)
    (dolist (date dates)
      (push (format "<th>%s</th>" (ssft-day-heading date)) rows))
    (push "</tr></thead><tbody>" rows)
    (dolist (slot slots)
      (push (format "<tr><th class=\"schedule-time\">%s</th>"
                    (ssft-minutes-to-time slot))
            rows)
      (dolist (date dates)
        (let ((events-at-slot (gethash (list date slot) starts))
              (is-covered (gethash (list date slot) covered)))
          (cond
           (events-at-slot
            (push (ssft-render-event-cell events-at-slot slot-minutes) rows))
           (is-covered
            nil)
           (t
            (push "<td class=\"schedule-empty\"></td>" rows)))))
      (push "</tr>" rows))
    (push "</tbody></table></div>" rows)
    (mapconcat #'identity (nreverse rows) "\n")))

(defun ssft-expand-generated-blocks ()
  (save-excursion
    (goto-char (point-min))
    (when (re-search-forward
           (concat "^" (regexp-quote "#+SSFT_TIMETABLE:") ".*$")
           nil t)
      (let ((start (match-beginning 0))
            (end (match-end 0))
            (html (ssft-render-schedule-html)))
        (delete-region start end)
        (goto-char start)
        (insert "#+BEGIN_EXPORT html\n" html "\n#+END_EXPORT")))))

(defun ssft-postprocess-index-html (target)
  (with-temp-buffer
    (insert-file-contents target)
    (save-excursion
      (goto-char (point-min))
      (when (search-forward "<nav id=\"table-of-contents\"" nil t)
        (let ((toc-start (match-beginning 0)))
          (when (search-forward "</nav>" nil t)
            (save-restriction
              (narrow-to-region toc-start (point))
              (goto-char (point-min))
              (cond
               ((search-forward "href=\"schedule.html\"" nil t)
                nil)
               ((progn
                  (goto-char (point-min))
                  (search-forward "href=\"#schedule\"" nil t))
                (replace-match "href=\"schedule.html\"" t t))
               (t
                (goto-char (point-min))
                (if (search-forward "<li><a href=\"#prev\"" nil t)
                    (progn
                      (beginning-of-line)
                      (insert "<li><a href=\"schedule.html\">Schedule</a></li>\n"))
                  (goto-char (point-max))
                  (when (search-backward "</ul>" nil t)
                    (insert "<li><a href=\"schedule.html\">Schedule</a></li>\n"))))))))))
    (write-region (point-min) (point-max) target nil 'silent)))

(defun ssft-export-file (root source target)
  (message "Exporting %s -> %s" source target)
  (let ((target-path (expand-file-name target root)))
    (with-temp-buffer
      (insert-file-contents (expand-file-name source root))
      (setq buffer-file-name (expand-file-name source root)
            default-directory root)
      (org-mode)
      (setq-local org-export-use-babel nil)
      (ssft-expand-generated-blocks)
      (org-export-to-file 'html target-path))
    (when (string= source "index.org")
      (ssft-postprocess-index-html target-path)))
  (message "Exported %s" target))

(let ((root (file-name-directory (or load-file-name buffer-file-name default-directory))))
  (dolist (page '(("index.org" . "index.html")
                  ("schedule.org" . "schedule.html")))
    (ssft-export-file root (car page) (cdr page))))
