(defun load-modal (modal-system  &aux file)
  ; Load the modal system X from the file "X.rrl".
      (if (setq file (open-read-modal modal-system "rrl")) then
	  (setq $history (read file))
	  (undo1 t)
	  (restore-properties (read file))
	  (restore-rest-globals (read file))
	  (close file)
	  (terpri)))



(defun open-read-modal (modal-system &optional suffix)
  ; Read in the file name and try to open it to read.
  ; Look for the file with the default suffix.
  (let (filename port)
   (setq filename modal-system)
   (cond  ((setq port
	    (or (car (errset (infile filename) nil))
		(car (errset (infile (string-downcase filename)) nil))
		(car (errset (infile (uconcat filename "." suffix)) nil))
		(car (errset (infile (string-downcase
				       (uconcat filename "." suffix))) nil))
		(car (errset (infile (uconcat $example-dir filename)) nil))
		(car (errset (infile (uconcat $example-dir
					    filename "." suffix)) nil)))))
	  (t (princ (uconcat "   Error : Couldn't open file: " filename))
	     (terpri)))
      port))

