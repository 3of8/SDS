; (echo "SMT Encoding for Randomized Social Choice")
; (echo "See the corresponding working paper by F. Brandl, F. Brandt, and C. Geist. Proving the incompatibility of efficiency and strategyproofness via SMT solving. 2015.")
; (echo "Weak individual preferences")
; (echo "Starting profile: ")
; (echo "1 agent : 0 ~ 2 > 1 ~ 3")
; (echo "1 agent : 1 ~ 3 > 0 ~ 2")
; (echo "1 agent : 0 ~ 3 > 1 > 2")
; (echo "1 agent : 1 ~ 2 > 0 > 3")
(set-logic QF_LRA)
(set-option :produce-proofs true)
; (echo "Lottery definitions")
(declare-fun p18a0 () Real)
(declare-fun p18a1 () Real)
(declare-fun p18a2 () Real)
(declare-fun p18a3 () Real)
(assert (>= p18a0 0.0))
(assert (>= p18a1 0.0))
(assert (>= p18a2 0.0))
(assert (>= p18a3 0.0))
(assert (= 1.0 (+ p18a0 p18a1 p18a2 p18a3)))
(declare-fun p112a0 () Real)
(declare-fun p112a1 () Real)
(declare-fun p112a2 () Real)
(declare-fun p112a3 () Real)
(assert (>= p112a0 0.0))
(assert (>= p112a1 0.0))
(assert (>= p112a2 0.0))
(assert (>= p112a3 0.0))
(assert (= 1.0 (+ p112a0 p112a1 p112a2 p112a3)))
(declare-fun p178a0 () Real)
(declare-fun p178a1 () Real)
(declare-fun p178a2 () Real)
(declare-fun p178a3 () Real)
(assert (>= p178a0 0.0))
(assert (>= p178a1 0.0))
(assert (>= p178a2 0.0))
(assert (>= p178a3 0.0))
(assert (= 1.0 (+ p178a0 p178a1 p178a2 p178a3)))
(declare-fun p174a0 () Real)
(declare-fun p174a1 () Real)
(declare-fun p174a2 () Real)
(declare-fun p174a3 () Real)
(assert (>= p174a0 0.0))
(assert (>= p174a1 0.0))
(assert (>= p174a2 0.0))
(assert (>= p174a3 0.0))
(assert (= 1.0 (+ p174a0 p174a1 p174a2 p174a3)))
(declare-fun p44a0 () Real)
(declare-fun p44a1 () Real)
(declare-fun p44a2 () Real)
(declare-fun p44a3 () Real)
(assert (>= p44a0 0.0))
(assert (>= p44a1 0.0))
(assert (>= p44a2 0.0))
(assert (>= p44a3 0.0))
(assert (= 1.0 (+ p44a0 p44a1 p44a2 p44a3)))
(declare-fun p91a0 () Real)
(declare-fun p91a1 () Real)
(declare-fun p91a2 () Real)
(declare-fun p91a3 () Real)
(assert (>= p91a0 0.0))
(assert (>= p91a1 0.0))
(assert (>= p91a2 0.0))
(assert (>= p91a3 0.0))
(assert (= 1.0 (+ p91a0 p91a1 p91a2 p91a3)))
(declare-fun p129a0 () Real)
(declare-fun p129a1 () Real)
(declare-fun p129a2 () Real)
(declare-fun p129a3 () Real)
(assert (>= p129a0 0.0))
(assert (>= p129a1 0.0))
(assert (>= p129a2 0.0))
(assert (>= p129a3 0.0))
(assert (= 1.0 (+ p129a0 p129a1 p129a2 p129a3)))
(declare-fun p175a0 () Real)
(declare-fun p175a1 () Real)
(declare-fun p175a2 () Real)
(declare-fun p175a3 () Real)
(assert (>= p175a0 0.0))
(assert (>= p175a1 0.0))
(assert (>= p175a2 0.0))
(assert (>= p175a3 0.0))
(assert (= 1.0 (+ p175a0 p175a1 p175a2 p175a3)))
(declare-fun p55a0 () Real)
(declare-fun p55a1 () Real)
(declare-fun p55a2 () Real)
(declare-fun p55a3 () Real)
(assert (>= p55a0 0.0))
(assert (>= p55a1 0.0))
(assert (>= p55a2 0.0))
(assert (>= p55a3 0.0))
(assert (= 1.0 (+ p55a0 p55a1 p55a2 p55a3)))
(declare-fun p0a0 () Real)
(declare-fun p0a1 () Real)
(declare-fun p0a2 () Real)
(declare-fun p0a3 () Real)
(assert (>= p0a0 0.0))
(assert (>= p0a1 0.0))
(assert (>= p0a2 0.0))
(assert (>= p0a3 0.0))
(assert (= 1.0 (+ p0a0 p0a1 p0a2 p0a3)))
(declare-fun p792a0 () Real)
(declare-fun p792a1 () Real)
(declare-fun p792a2 () Real)
(declare-fun p792a3 () Real)
(assert (>= p792a0 0.0))
(assert (>= p792a1 0.0))
(assert (>= p792a2 0.0))
(assert (>= p792a3 0.0))
(assert (= 1.0 (+ p792a0 p792a1 p792a2 p792a3)))
(declare-fun p42a0 () Real)
(declare-fun p42a1 () Real)
(declare-fun p42a2 () Real)
(declare-fun p42a3 () Real)
(assert (>= p42a0 0.0))
(assert (>= p42a1 0.0))
(assert (>= p42a2 0.0))
(assert (>= p42a3 0.0))
(assert (= 1.0 (+ p42a0 p42a1 p42a2 p42a3)))
(declare-fun p114a0 () Real)
(declare-fun p114a1 () Real)
(declare-fun p114a2 () Real)
(declare-fun p114a3 () Real)
(assert (>= p114a0 0.0))
(assert (>= p114a1 0.0))
(assert (>= p114a2 0.0))
(assert (>= p114a3 0.0))
(assert (= 1.0 (+ p114a0 p114a1 p114a2 p114a3)))
(declare-fun p654a0 () Real)
(declare-fun p654a1 () Real)
(declare-fun p654a2 () Real)
(declare-fun p654a3 () Real)
(assert (>= p654a0 0.0))
(assert (>= p654a1 0.0))
(assert (>= p654a2 0.0))
(assert (>= p654a3 0.0))
(assert (= 1.0 (+ p654a0 p654a1 p654a2 p654a3)))
(declare-fun p7a0 () Real)
(declare-fun p7a1 () Real)
(declare-fun p7a2 () Real)
(declare-fun p7a3 () Real)
(assert (>= p7a0 0.0))
(assert (>= p7a1 0.0))
(assert (>= p7a2 0.0))
(assert (>= p7a3 0.0))
(assert (= 1.0 (+ p7a0 p7a1 p7a2 p7a3)))
(declare-fun p127a0 () Real)
(declare-fun p127a1 () Real)
(declare-fun p127a2 () Real)
(declare-fun p127a3 () Real)
(assert (>= p127a0 0.0))
(assert (>= p127a1 0.0))
(assert (>= p127a2 0.0))
(assert (>= p127a3 0.0))
(assert (= 1.0 (+ p127a0 p127a1 p127a2 p127a3)))
(declare-fun p88a0 () Real)
(declare-fun p88a1 () Real)
(declare-fun p88a2 () Real)
(declare-fun p88a3 () Real)
(assert (>= p88a0 0.0))
(assert (>= p88a1 0.0))
(assert (>= p88a2 0.0))
(assert (>= p88a3 0.0))
(assert (= 1.0 (+ p88a0 p88a1 p88a2 p88a3)))
(declare-fun p573a0 () Real)
(declare-fun p573a1 () Real)
(declare-fun p573a2 () Real)
(declare-fun p573a3 () Real)
(assert (>= p573a0 0.0))
(assert (>= p573a1 0.0))
(assert (>= p573a2 0.0))
(assert (>= p573a3 0.0))
(assert (= 1.0 (+ p573a0 p573a1 p573a2 p573a3)))
(declare-fun p6a0 () Real)
(declare-fun p6a1 () Real)
(declare-fun p6a2 () Real)
(declare-fun p6a3 () Real)
(assert (>= p6a0 0.0))
(assert (>= p6a1 0.0))
(assert (>= p6a2 0.0))
(assert (>= p6a3 0.0))
(assert (= 1.0 (+ p6a0 p6a1 p6a2 p6a3)))
(declare-fun p591a0 () Real)
(declare-fun p591a1 () Real)
(declare-fun p591a2 () Real)
(declare-fun p591a3 () Real)
(assert (>= p591a0 0.0))
(assert (>= p591a1 0.0))
(assert (>= p591a2 0.0))
(assert (>= p591a3 0.0))
(assert (= 1.0 (+ p591a0 p591a1 p591a2 p591a3)))
(declare-fun p625a0 () Real)
(declare-fun p625a1 () Real)
(declare-fun p625a2 () Real)
(declare-fun p625a3 () Real)
(assert (>= p625a0 0.0))
(assert (>= p625a1 0.0))
(assert (>= p625a2 0.0))
(assert (>= p625a3 0.0))
(assert (= 1.0 (+ p625a0 p625a1 p625a2 p625a3)))
(declare-fun p642a0 () Real)
(declare-fun p642a1 () Real)
(declare-fun p642a2 () Real)
(declare-fun p642a3 () Real)
(assert (>= p642a0 0.0))
(assert (>= p642a1 0.0))
(assert (>= p642a2 0.0))
(assert (>= p642a3 0.0))
(assert (= 1.0 (+ p642a0 p642a1 p642a2 p642a3)))
(declare-fun p85a0 () Real)
(declare-fun p85a1 () Real)
(declare-fun p85a2 () Real)
(declare-fun p85a3 () Real)
(assert (>= p85a0 0.0))
(assert (>= p85a1 0.0))
(assert (>= p85a2 0.0))
(assert (>= p85a3 0.0))
(assert (= 1.0 (+ p85a0 p85a1 p85a2 p85a3)))
(declare-fun p608a0 () Real)
(declare-fun p608a1 () Real)
(declare-fun p608a2 () Real)
(declare-fun p608a3 () Real)
(assert (>= p608a0 0.0))
(assert (>= p608a1 0.0))
(assert (>= p608a2 0.0))
(assert (>= p608a3 0.0))
(assert (= 1.0 (+ p608a0 p608a1 p608a2 p608a3)))
(declare-fun p22a0 () Real)
(declare-fun p22a1 () Real)
(declare-fun p22a2 () Real)
(declare-fun p22a3 () Real)
(assert (>= p22a0 0.0))
(assert (>= p22a1 0.0))
(assert (>= p22a2 0.0))
(assert (>= p22a3 0.0))
(assert (= 1.0 (+ p22a0 p22a1 p22a2 p22a3)))
(declare-fun p333a0 () Real)
(declare-fun p333a1 () Real)
(declare-fun p333a2 () Real)
(declare-fun p333a3 () Real)
(assert (>= p333a0 0.0))
(assert (>= p333a1 0.0))
(assert (>= p333a2 0.0))
(assert (>= p333a3 0.0))
(assert (= 1.0 (+ p333a0 p333a1 p333a2 p333a3)))
(declare-fun p80a0 () Real)
(declare-fun p80a1 () Real)
(declare-fun p80a2 () Real)
(declare-fun p80a3 () Real)
(assert (>= p80a0 0.0))
(assert (>= p80a1 0.0))
(assert (>= p80a2 0.0))
(assert (>= p80a3 0.0))
(assert (= 1.0 (+ p80a0 p80a1 p80a2 p80a3)))
(declare-fun p249a0 () Real)
(declare-fun p249a1 () Real)
(declare-fun p249a2 () Real)
(declare-fun p249a3 () Real)
(assert (>= p249a0 0.0))
(assert (>= p249a1 0.0))
(assert (>= p249a2 0.0))
(assert (>= p249a3 0.0))
(assert (= 1.0 (+ p249a0 p249a1 p249a2 p249a3)))
(declare-fun p12a0 () Real)
(declare-fun p12a1 () Real)
(declare-fun p12a2 () Real)
(declare-fun p12a3 () Real)
(assert (>= p12a0 0.0))
(assert (>= p12a1 0.0))
(assert (>= p12a2 0.0))
(assert (>= p12a3 0.0))
(assert (= 1.0 (+ p12a0 p12a1 p12a2 p12a3)))
(declare-fun p624a0 () Real)
(declare-fun p624a1 () Real)
(declare-fun p624a2 () Real)
(declare-fun p624a3 () Real)
(assert (>= p624a0 0.0))
(assert (>= p624a1 0.0))
(assert (>= p624a2 0.0))
(assert (>= p624a3 0.0))
(assert (= 1.0 (+ p624a0 p624a1 p624a2 p624a3)))
(declare-fun p48a0 () Real)
(declare-fun p48a1 () Real)
(declare-fun p48a2 () Real)
(declare-fun p48a3 () Real)
(assert (>= p48a0 0.0))
(assert (>= p48a1 0.0))
(assert (>= p48a2 0.0))
(assert (>= p48a3 0.0))
(assert (= 1.0 (+ p48a0 p48a1 p48a2 p48a3)))
(declare-fun p641a0 () Real)
(declare-fun p641a1 () Real)
(declare-fun p641a2 () Real)
(declare-fun p641a3 () Real)
(assert (>= p641a0 0.0))
(assert (>= p641a1 0.0))
(assert (>= p641a2 0.0))
(assert (>= p641a3 0.0))
(assert (= 1.0 (+ p641a0 p641a1 p641a2 p641a3)))
(declare-fun p30a0 () Real)
(declare-fun p30a1 () Real)
(declare-fun p30a2 () Real)
(declare-fun p30a3 () Real)
(assert (>= p30a0 0.0))
(assert (>= p30a1 0.0))
(assert (>= p30a2 0.0))
(assert (>= p30a3 0.0))
(assert (= 1.0 (+ p30a0 p30a1 p30a2 p30a3)))
(declare-fun p285a0 () Real)
(declare-fun p285a1 () Real)
(declare-fun p285a2 () Real)
(declare-fun p285a3 () Real)
(assert (>= p285a0 0.0))
(assert (>= p285a1 0.0))
(assert (>= p285a2 0.0))
(assert (>= p285a3 0.0))
(assert (= 1.0 (+ p285a0 p285a1 p285a2 p285a3)))
(declare-fun p496a0 () Real)
(declare-fun p496a1 () Real)
(declare-fun p496a2 () Real)
(declare-fun p496a3 () Real)
(assert (>= p496a0 0.0))
(assert (>= p496a1 0.0))
(assert (>= p496a2 0.0))
(assert (>= p496a3 0.0))
(assert (= 1.0 (+ p496a0 p496a1 p496a2 p496a3)))
(declare-fun p3a0 () Real)
(declare-fun p3a1 () Real)
(declare-fun p3a2 () Real)
(declare-fun p3a3 () Real)
(assert (>= p3a0 0.0))
(assert (>= p3a1 0.0))
(assert (>= p3a2 0.0))
(assert (>= p3a3 0.0))
(assert (= 1.0 (+ p3a0 p3a1 p3a2 p3a3)))
(declare-fun p335a0 () Real)
(declare-fun p335a1 () Real)
(declare-fun p335a2 () Real)
(declare-fun p335a3 () Real)
(assert (>= p335a0 0.0))
(assert (>= p335a1 0.0))
(assert (>= p335a2 0.0))
(assert (>= p335a3 0.0))
(assert (= 1.0 (+ p335a0 p335a1 p335a2 p335a3)))
(declare-fun p248a0 () Real)
(declare-fun p248a1 () Real)
(declare-fun p248a2 () Real)
(declare-fun p248a3 () Real)
(assert (>= p248a0 0.0))
(assert (>= p248a1 0.0))
(assert (>= p248a2 0.0))
(assert (>= p248a3 0.0))
(assert (= 1.0 (+ p248a0 p248a1 p248a2 p248a3)))
(declare-fun p9a0 () Real)
(declare-fun p9a1 () Real)
(declare-fun p9a2 () Real)
(declare-fun p9a3 () Real)
(assert (>= p9a0 0.0))
(assert (>= p9a1 0.0))
(assert (>= p9a2 0.0))
(assert (>= p9a3 0.0))
(assert (= 1.0 (+ p9a0 p9a1 p9a2 p9a3)))
(declare-fun p489a0 () Real)
(declare-fun p489a1 () Real)
(declare-fun p489a2 () Real)
(declare-fun p489a3 () Real)
(assert (>= p489a0 0.0))
(assert (>= p489a1 0.0))
(assert (>= p489a2 0.0))
(assert (>= p489a3 0.0))
(assert (= 1.0 (+ p489a0 p489a1 p489a2 p489a3)))
(declare-fun p409a0 () Real)
(declare-fun p409a1 () Real)
(declare-fun p409a2 () Real)
(declare-fun p409a3 () Real)
(assert (>= p409a0 0.0))
(assert (>= p409a1 0.0))
(assert (>= p409a2 0.0))
(assert (>= p409a3 0.0))
(assert (= 1.0 (+ p409a0 p409a1 p409a2 p409a3)))
(declare-fun p130a0 () Real)
(declare-fun p130a1 () Real)
(declare-fun p130a2 () Real)
(declare-fun p130a3 () Real)
(assert (>= p130a0 0.0))
(assert (>= p130a1 0.0))
(assert (>= p130a2 0.0))
(assert (>= p130a3 0.0))
(assert (= 1.0 (+ p130a0 p130a1 p130a2 p130a3)))
(declare-fun p548a0 () Real)
(declare-fun p548a1 () Real)
(declare-fun p548a2 () Real)
(declare-fun p548a3 () Real)
(assert (>= p548a0 0.0))
(assert (>= p548a1 0.0))
(assert (>= p548a2 0.0))
(assert (>= p548a3 0.0))
(assert (= 1.0 (+ p548a0 p548a1 p548a2 p548a3)))
(declare-fun p108a0 () Real)
(declare-fun p108a1 () Real)
(declare-fun p108a2 () Real)
(declare-fun p108a3 () Real)
(assert (>= p108a0 0.0))
(assert (>= p108a1 0.0))
(assert (>= p108a2 0.0))
(assert (>= p108a3 0.0))
(assert (= 1.0 (+ p108a0 p108a1 p108a2 p108a3)))
(declare-fun p135a0 () Real)
(declare-fun p135a1 () Real)
(declare-fun p135a2 () Real)
(declare-fun p135a3 () Real)
(assert (>= p135a0 0.0))
(assert (>= p135a1 0.0))
(assert (>= p135a2 0.0))
(assert (>= p135a3 0.0))
(assert (= 1.0 (+ p135a0 p135a1 p135a2 p135a3)))
(declare-fun p377a0 () Real)
(declare-fun p377a1 () Real)
(declare-fun p377a2 () Real)
(declare-fun p377a3 () Real)
(assert (>= p377a0 0.0))
(assert (>= p377a1 0.0))
(assert (>= p377a2 0.0))
(assert (>= p377a3 0.0))
(assert (= 1.0 (+ p377a0 p377a1 p377a2 p377a3)))
(declare-fun p58a0 () Real)
(declare-fun p58a1 () Real)
(declare-fun p58a2 () Real)
(declare-fun p58a3 () Real)
(assert (>= p58a0 0.0))
(assert (>= p58a1 0.0))
(assert (>= p58a2 0.0))
(assert (>= p58a3 0.0))
(assert (= 1.0 (+ p58a0 p58a1 p58a2 p58a3)))
; (echo "weak_SD-strategyproofness with maximum distance 1")
(assert (! (or (< (+ p6a0 p6a2) (+ p0a0 p0a2)) (< (+ p6a0 p6a2 p6a3) (+ p0a0 p0a2 p0a3)) (and (= (+ p6a0 p6a2) (+ p0a0 p0a2)) (= (+ p6a0 p6a2 p6a3) (+ p0a0 p0a2 p0a3)))) :named weak_SD-strategyproofness_8))
; This manipulation was obtained from p0:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; To:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 2 > 1 ~ 3
; By replacing voter 0 ~ 2 > 3 > 1 with 0 ~ 2 > 1 ~ 3
; The manipulated profile in canonical form is p6:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 2 > 1 ~ 3
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
; (echo "weak_SD-strategyproofness with maximum distance 2")
(assert (! (<= (+ p9a2 p9a3) (+ p3a2 p3a3)) :named weak_SD-strategyproofness_14))
; This manipulation was obtained from p3:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; To:
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 > 1
; By replacing voter 2 ~ 3 > 0 ~ 1 with 2 ~ 3 > 0 > 1
; The manipulated profile in canonical form is p9:
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 > 1
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< p0a0 p3a0) (< (+ p0a0 p0a1) (+ p3a0 p3a1)) (and (= p0a0 p3a0) (= (+ p0a0 p0a1) (+ p3a0 p3a1)))) :named weak_SD-strategyproofness_40))
; This manipulation was obtained from p3:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; To:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 1 > 2 ~ 3
; By replacing voter 0 > 1 > 2 ~ 3 with 0 ~ 1 > 2 ~ 3
; The manipulated profile in canonical form is p0:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (<= (+ p18a0 p18a1) (+ p6a0 p6a1)) :named weak_SD-strategyproofness_120))
; This manipulation was obtained from p6:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 2 > 1 ~ 3
; To:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 0 > 1 > 2 ~ 3
; By replacing voter 0 ~ 1 > 2 ~ 3 with 0 > 1 > 2 ~ 3
; The manipulated profile in canonical form is p18:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 0 ~ 2 > 1 ~ 3
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (<= (+ p80a2 p80a3) (+ p6a2 p6a3)) :named weak_SD-strategyproofness_126))
; This manipulation was obtained from p6:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 2 > 1 ~ 3
; To:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 2 ~ 3 > 0 > 1
; By replacing voter 2 ~ 3 > 0 ~ 1 with 2 ~ 3 > 0 > 1
; The manipulated profile in canonical form is p80:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 2 ~ 3 > 0 > 1
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (<= (+ p114a1 p114a3) (+ p7a2 p7a3)) :named weak_SD-strategyproofness_194))
; This manipulation was obtained from p7:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 2 > 3 > 1
; To:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 2 > 3 > 1
; 1 agent : 2 ~ 3 > 0 > 1
; By replacing voter 2 ~ 3 > 0 ~ 1 with 2 ~ 3 > 0 > 1
; The manipulated profile in canonical form is p114:
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 2 ~ 3 > 0 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 3 > 2
; It can be obtained via isomorphism: {0=0, 1=2, 2=1, 3=3}
(assert (! (or (< (+ p129a1 p129a3) (+ p7a1 p7a3)) (< (+ p129a0 p129a1 p129a3) (+ p7a0 p7a1 p7a3)) (and (= (+ p129a1 p129a3) (+ p7a1 p7a3)) (= (+ p129a0 p129a1 p129a3) (+ p7a0 p7a1 p7a3)))) :named weak_SD-strategyproofness_206))
; This manipulation was obtained from p7:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 2 > 3 > 1
; To:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 > 2 > 3 > 1
; 1 agent : 3 > 0 ~ 1 > 2
; By replacing voter 1 ~ 3 > 0 > 2 with 3 > 0 ~ 1 > 2
; The manipulated profile in canonical form is p129:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 > 2 > 3 > 1
; 1 agent : 3 > 0 ~ 1 > 2
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< p44a3 p7a0) (< (+ p44a3 p44a1) (+ p7a0 p7a2)) (< (+ p44a3 p44a1 p44a0) (+ p7a0 p7a2 p7a3)) (and (= p44a3 p7a0) (= (+ p44a3 p44a1) (+ p7a0 p7a2)) (= (+ p44a3 p44a1 p44a0) (+ p7a0 p7a2 p7a3)))) :named weak_SD-strategyproofness_213))
; This manipulation was obtained from p7:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 2 > 3 > 1
; To:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 2 ~ 3 > 1
; By replacing voter 0 > 2 > 3 > 1 with 0 > 2 ~ 3 > 1
; The manipulated profile in canonical form is p44:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 3 > 0 ~ 1 > 2
; It can be obtained via isomorphism: {0=3, 1=2, 2=1, 3=0}
; (echo "weak_SD-strategyproofness with maximum distance 1")
(assert (! (<= (+ p178a0 p178a2) (+ p88a0 p88a2)) :named weak_SD-strategyproofness_296))
; This manipulation was obtained from p88:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 3 > 0 ~ 1 > 2
; To:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 3 > 0 ~ 1 > 2
; 1 agent : 2 > 0 > 1 ~ 3
; By replacing voter 0 ~ 2 > 1 ~ 3 with 2 > 0 > 1 ~ 3
; The manipulated profile in canonical form is p178:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 3 > 0 ~ 1 > 2
; 1 agent : 2 > 0 > 1 ~ 3
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (<= (+ p248a0 p248a2) (+ p112a0 p112a2)) :named weak_SD-strategyproofness_452))
; This manipulation was obtained from p112:
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 2 ~ 3 > 0 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; To:
; 1 agent : 2 ~ 3 > 0 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 0 ~ 2 > 1 > 3
; By replacing voter 0 ~ 2 > 1 ~ 3 with 0 ~ 2 > 1 > 3
; The manipulated profile in canonical form is p248:
; 1 agent : 2 ~ 3 > 0 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 0 ~ 2 > 1 > 3
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< (+ p18a2 p18a3) (+ p112a2 p112a3)) (< (+ p18a0 p18a2 p18a3) (+ p112a0 p112a2 p112a3)) (and (= (+ p18a2 p18a3) (+ p112a2 p112a3)) (= (+ p18a0 p18a2 p18a3) (+ p112a0 p112a2 p112a3)))) :named weak_SD-strategyproofness_456))
; This manipulation was obtained from p112:
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 2 ~ 3 > 0 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; To:
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; By replacing voter 2 ~ 3 > 0 > 1 with 2 ~ 3 > 0 ~ 1
; The manipulated profile in canonical form is p18:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 0 ~ 2 > 1 ~ 3
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< (+ p7a2 p7a3) (+ p114a1 p114a3)) (< (+ p7a0 p7a2 p7a3) (+ p114a0 p114a1 p114a3)) (and (= (+ p7a2 p7a3) (+ p114a1 p114a3)) (= (+ p7a0 p7a2 p7a3) (+ p114a0 p114a1 p114a3)))) :named weak_SD-strategyproofness_731))
; This manipulation was obtained from p114:
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 2 ~ 3 > 0 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 3 > 2
; To:
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 2 ~ 3 > 0 > 1
; 1 agent : 0 > 1 > 3 > 2
; 1 agent : 1 ~ 3 > 0 ~ 2
; By replacing voter 1 ~ 3 > 0 > 2 with 1 ~ 3 > 0 ~ 2
; The manipulated profile in canonical form is p7:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 2 > 3 > 1
; It can be obtained via isomorphism: {0=0, 1=2, 2=1, 3=3}
(assert (! (or (< (+ p88a0 p88a2) (+ p44a0 p44a2)) (< (+ p88a0 p88a2 p88a3) (+ p44a0 p44a2 p44a3)) (and (= (+ p88a0 p88a2) (+ p44a0 p44a2)) (= (+ p88a0 p88a2 p88a3) (+ p44a0 p44a2 p44a3)))) :named weak_SD-strategyproofness_882))
; This manipulation was obtained from p44:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 3 > 0 ~ 1 > 2
; To:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 3 > 0 ~ 1 > 2
; 1 agent : 0 ~ 2 > 1 ~ 3
; By replacing voter 0 ~ 2 > 3 > 1 with 0 ~ 2 > 1 ~ 3
; The manipulated profile in canonical form is p88:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 3 > 0 ~ 1 > 2
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (<= (+ p112a2 p112a3) (+ p18a2 p18a3)) :named weak_SD-strategyproofness_939))
; This manipulation was obtained from p18:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 0 ~ 2 > 1 ~ 3
; To:
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 2 ~ 3 > 0 > 1
; By replacing voter 2 ~ 3 > 0 ~ 1 with 2 ~ 3 > 0 > 1
; The manipulated profile in canonical form is p112:
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 2 ~ 3 > 0 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< p6a0 p18a0) (< (+ p6a0 p6a1) (+ p18a0 p18a1)) (and (= p6a0 p18a0) (= (+ p6a0 p6a1) (+ p18a0 p18a1)))) :named weak_SD-strategyproofness_946))
; This manipulation was obtained from p18:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 0 ~ 2 > 1 ~ 3
; To:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 0 ~ 1 > 2 ~ 3
; By replacing voter 0 > 1 > 2 ~ 3 with 0 ~ 1 > 2 ~ 3
; The manipulated profile in canonical form is p6:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 2 > 1 ~ 3
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< (+ p112a0 p112a2) (+ p9a0 p9a2)) (< (+ p112a0 p112a2 p112a3) (+ p9a0 p9a2 p9a3)) (and (= (+ p112a0 p112a2) (+ p9a0 p9a2)) (= (+ p112a0 p112a2 p112a3) (+ p9a0 p9a2 p9a3)))) :named weak_SD-strategyproofness_1016))
; This manipulation was obtained from p9:
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 > 1
; To:
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 > 1
; 1 agent : 0 ~ 2 > 1 ~ 3
; By replacing voter 0 ~ 2 > 3 > 1 with 0 ~ 2 > 1 ~ 3
; The manipulated profile in canonical form is p112:
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 2 ~ 3 > 0 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (<= (+ p489a3 p489a2) (+ p108a2 p108a3)) :named weak_SD-strategyproofness_1163))
; This manipulation was obtained from p108:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 0 ~ 1 > 3 > 2
; 1 agent : 0 ~ 1 ~ 3 > 2
; To:
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 0 ~ 1 > 3 > 2
; 1 agent : 0 ~ 1 ~ 3 > 2
; 1 agent : 2 > 3 > 0 ~ 1
; By replacing voter 2 ~ 3 > 0 ~ 1 with 2 > 3 > 0 ~ 1
; The manipulated profile in canonical form is p489:
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 0 ~ 1 > 2 > 3
; 1 agent : 0 ~ 1 ~ 2 > 3
; 1 agent : 3 > 2 > 0 ~ 1
; It can be obtained via isomorphism: {0=0, 1=1, 2=3, 3=2}
(assert (! (or (< (+ p42a0 p42a1) (+ p108a0 p108a1)) (< (+ p42a0 p42a1 p42a3) (+ p108a0 p108a1 p108a3)) (and (= (+ p42a0 p42a1) (+ p108a0 p108a1)) (= (+ p42a0 p42a1 p42a3) (+ p108a0 p108a1 p108a3)))) :named weak_SD-strategyproofness_1168))
; This manipulation was obtained from p108:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 0 ~ 1 > 3 > 2
; 1 agent : 0 ~ 1 ~ 3 > 2
; To:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 0 ~ 1 ~ 3 > 2
; 1 agent : 0 ~ 1 > 2 ~ 3
; By replacing voter 0 ~ 1 > 3 > 2 with 0 ~ 1 > 2 ~ 3
; The manipulated profile in canonical form is p42:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 0 ~ 1 ~ 3 > 2
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< p548a0 p129a0) (< (+ p548a0 p548a2) (+ p129a0 p129a2)) (< (+ p548a0 p548a2 p548a3) (+ p129a0 p129a2 p129a3)) (and (= p548a0 p129a0) (= (+ p548a0 p548a2) (+ p129a0 p129a2)) (= (+ p548a0 p548a2 p548a3) (+ p129a0 p129a2 p129a3)))) :named weak_SD-strategyproofness_1353))
; This manipulation was obtained from p129:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 > 2 > 3 > 1
; 1 agent : 3 > 0 ~ 1 > 2
; To:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 3 > 0 ~ 1 > 2
; 1 agent : 0 > 2 ~ 3 > 1
; By replacing voter 0 > 2 > 3 > 1 with 0 > 2 ~ 3 > 1
; The manipulated profile in canonical form is p548:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 3 > 0 ~ 1 > 2
; 1 agent : 0 > 2 ~ 3 > 1
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< (+ p6a2 p6a3) (+ p80a1 p80a3)) (< (+ p6a0 p6a2 p6a3) (+ p80a0 p80a1 p80a3)) (and (= (+ p6a2 p6a3) (+ p80a1 p80a3)) (= (+ p6a0 p6a2 p6a3) (+ p80a0 p80a1 p80a3)))) :named weak_SD-strategyproofness_1373))
; This manipulation was obtained from p80:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 2 ~ 3 > 0 > 1
; To:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 2 ~ 3 > 0 > 1
; 1 agent : 1 ~ 3 > 0 ~ 2
; By replacing voter 1 ~ 3 > 0 > 2 with 1 ~ 3 > 0 ~ 2
; The manipulated profile in canonical form is p6:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 2 > 1 ~ 3
; It can be obtained via isomorphism: {0=0, 1=2, 2=1, 3=3}
(assert (! (<= (+ p573a3 p573a2) (+ p85a2 p85a3)) :named weak_SD-strategyproofness_1476))
; This manipulation was obtained from p85:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 0 ~ 1 ~ 3 > 2
; To:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 0 ~ 1 ~ 3 > 2
; 1 agent : 2 > 3 > 0 ~ 1
; By replacing voter 2 ~ 3 > 0 ~ 1 with 2 > 3 > 0 ~ 1
; The manipulated profile in canonical form is p573:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 3 > 1 ~ 2
; 1 agent : 0 ~ 1 ~ 2 > 3
; 1 agent : 3 > 2 > 0 ~ 1
; It can be obtained via isomorphism: {0=0, 1=1, 2=3, 3=2}
(assert (! (<= (+ p42a0 p42a2) (+ p85a0 p85a2)) :named weak_SD-strategyproofness_1479))
; This manipulation was obtained from p85:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 0 ~ 1 ~ 3 > 2
; To:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 1 ~ 3 > 2
; 1 agent : 0 ~ 2 > 3 > 1
; By replacing voter 0 ~ 2 > 1 ~ 3 with 0 ~ 2 > 3 > 1
; The manipulated profile in canonical form is p42:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 0 ~ 1 ~ 3 > 2
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (<= (+ p608a0 p608a1) (+ p130a0 p130a1)) :named weak_SD-strategyproofness_1642))
; This manipulation was obtained from p130:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 3 > 1 > 0 > 2
; 1 agent : 2 > 0 > 1 ~ 3
; To:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 3 > 1 > 0 > 2
; 1 agent : 2 > 0 > 1 ~ 3
; 1 agent : 1 > 0 > 2 ~ 3
; By replacing voter 0 ~ 1 > 2 ~ 3 with 1 > 0 > 2 ~ 3
; The manipulated profile in canonical form is p608:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 3 > 1 > 0 > 2
; 1 agent : 2 > 0 > 1 ~ 3
; 1 agent : 1 > 0 > 2 ~ 3
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< p178a3 p130a3) (< (+ p178a1 p178a3) (+ p130a1 p130a3)) (< (+ p178a0 p178a1 p178a3) (+ p130a0 p130a1 p130a3)) (and (= p178a3 p130a3) (= (+ p178a1 p178a3) (+ p130a1 p130a3)) (= (+ p178a0 p178a1 p178a3) (+ p130a0 p130a1 p130a3)))) :named weak_SD-strategyproofness_1644))
; This manipulation was obtained from p130:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 3 > 1 > 0 > 2
; 1 agent : 2 > 0 > 1 ~ 3
; To:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 > 0 > 1 ~ 3
; 1 agent : 3 > 0 ~ 1 > 2
; By replacing voter 3 > 1 > 0 > 2 with 3 > 0 ~ 1 > 2
; The manipulated profile in canonical form is p178:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 3 > 0 ~ 1 > 2
; 1 agent : 2 > 0 > 1 ~ 3
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (<= (+ p624a0 p624a1) (+ p58a0 p58a1)) :named weak_SD-strategyproofness_1779))
; This manipulation was obtained from p58:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 2 > 0 ~ 1 > 3
; To:
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 2 > 0 ~ 1 > 3
; 1 agent : 0 ~ 1 > 3 > 2
; By replacing voter 0 ~ 1 > 2 ~ 3 with 0 ~ 1 > 3 > 2
; The manipulated profile in canonical form is p624:
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 2 > 0 ~ 1 > 3
; 1 agent : 0 ~ 1 > 3 > 2
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (<= (+ p130a0 p130a2) (+ p91a0 p91a2)) :named weak_SD-strategyproofness_1883))
; This manipulation was obtained from p91:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 3 > 1 > 0 > 2
; To:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 3 > 1 > 0 > 2
; 1 agent : 2 > 0 > 1 ~ 3
; By replacing voter 0 ~ 2 > 1 ~ 3 with 2 > 0 > 1 ~ 3
; The manipulated profile in canonical form is p130:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 3 > 1 > 0 > 2
; 1 agent : 2 > 0 > 1 ~ 3
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< p6a3 p91a3) (< (+ p6a1 p6a3) (+ p91a1 p91a3)) (< (+ p6a0 p6a1 p6a3) (+ p91a0 p91a1 p91a3)) (and (= p6a3 p91a3) (= (+ p6a1 p6a3) (+ p91a1 p91a3)) (= (+ p6a0 p6a1 p6a3) (+ p91a0 p91a1 p91a3)))) :named weak_SD-strategyproofness_1884))
; This manipulation was obtained from p91:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 3 > 1 > 0 > 2
; To:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 1 ~ 3 > 0 > 2
; By replacing voter 3 > 1 > 0 > 2 with 1 ~ 3 > 0 > 2
; The manipulated profile in canonical form is p6:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 2 > 1 ~ 3
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< (+ p127a0 p127a2) (+ p42a0 p42a2)) (< (+ p127a0 p127a2 p127a3) (+ p42a0 p42a2 p42a3)) (and (= (+ p127a0 p127a2) (+ p42a0 p42a2)) (= (+ p127a0 p127a2 p127a3) (+ p42a0 p42a2 p42a3)))) :named weak_SD-strategyproofness_1959))
; This manipulation was obtained from p42:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 0 ~ 1 ~ 3 > 2
; To:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 1 ~ 3 > 2
; 1 agent : 0 > 2 > 3 > 1
; By replacing voter 0 ~ 2 > 3 > 1 with 0 > 2 > 3 > 1
; The manipulated profile in canonical form is p127:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 > 2 > 3 > 1
; 1 agent : 0 ~ 1 ~ 3 > 2
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (<= (+ p489a0 p489a1) (+ p55a0 p55a1)) :named weak_SD-strategyproofness_2087))
; This manipulation was obtained from p55:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 0 ~ 1 ~ 2 > 3
; To:
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 0 ~ 1 ~ 2 > 3
; 1 agent : 0 ~ 1 > 2 > 3
; By replacing voter 0 ~ 1 > 2 ~ 3 with 0 ~ 1 > 2 > 3
; The manipulated profile in canonical form is p489:
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 0 ~ 1 > 2 > 3
; 1 agent : 0 ~ 1 ~ 2 > 3
; 1 agent : 3 > 2 > 0 ~ 1
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< (+ p573a0 p573a3) (+ p55a0 p55a3)) (< (+ p573a0 p573a2 p573a3) (+ p55a0 p55a2 p55a3)) (and (= (+ p573a0 p573a3) (+ p55a0 p55a3)) (= (+ p573a0 p573a2 p573a3) (+ p55a0 p55a2 p55a3)))) :named weak_SD-strategyproofness_2091))
; This manipulation was obtained from p55:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 0 ~ 1 ~ 2 > 3
; To:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 0 ~ 1 ~ 2 > 3
; 1 agent : 0 ~ 3 > 1 ~ 2
; By replacing voter 0 ~ 3 > 2 > 1 with 0 ~ 3 > 1 ~ 2
; The manipulated profile in canonical form is p573:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 3 > 1 ~ 2
; 1 agent : 0 ~ 1 ~ 2 > 3
; 1 agent : 3 > 2 > 0 ~ 1
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (<= (+ p642a2 p642a3) (+ p30a2 p30a3)) :named weak_SD-strategyproofness_2227))
; This manipulation was obtained from p30:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 3 > 0 ~ 1 > 2
; To:
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 3 > 0 ~ 1 > 2
; 1 agent : 3 > 2 > 0 ~ 1
; By replacing voter 2 ~ 3 > 0 ~ 1 with 3 > 2 > 0 ~ 1
; The manipulated profile in canonical form is p642:
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 3 > 0 ~ 1 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< p44a0 p30a0) (< (+ p44a0 p44a1) (+ p30a0 p30a1)) (and (= p44a0 p30a0) (= (+ p44a0 p44a1) (+ p30a0 p30a1)))) :named weak_SD-strategyproofness_2231))
; This manipulation was obtained from p30:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 3 > 0 ~ 1 > 2
; To:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 3 > 0 ~ 1 > 2
; 1 agent : 0 ~ 1 > 2 ~ 3
; By replacing voter 0 > 1 > 2 ~ 3 with 0 ~ 1 > 2 ~ 3
; The manipulated profile in canonical form is p44:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 3 > 0 ~ 1 > 2
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< (+ p333a1 p333a3) (+ p22a1 p22a3)) (< (+ p333a0 p333a1 p333a3) (+ p22a0 p22a1 p22a3)) (and (= (+ p333a1 p333a3) (+ p22a1 p22a3)) (= (+ p333a0 p333a1 p333a3) (+ p22a0 p22a1 p22a3)))) :named weak_SD-strategyproofness_2304))
; This manipulation was obtained from p22:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 0 > 2 > 1 ~ 3
; To:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 0 > 2 > 1 ~ 3
; 1 agent : 1 ~ 3 > 0 ~ 2
; By replacing voter 1 ~ 3 > 0 > 2 with 1 ~ 3 > 0 ~ 2
; The manipulated profile in canonical form is p333:
; 1 agent : 1 ~ 3 > 0 ~ 2
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 0 > 2 > 1 ~ 3
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
; (echo "weak_SD-strategyproofness with maximum distance 2")
(assert (! (<= (+ p129a0 p129a2) (+ p88a0 p88a2)) :named weak_SD-strategyproofness_2597))
; This manipulation was obtained from p88:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 3 > 0 ~ 1 > 2
; To:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 3 > 0 ~ 1 > 2
; 1 agent : 0 > 2 > 3 > 1
; By replacing voter 0 ~ 2 > 1 ~ 3 with 0 > 2 > 3 > 1
; The manipulated profile in canonical form is p129:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 > 2 > 3 > 1
; 1 agent : 3 > 0 ~ 1 > 2
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (<= (+ p792a0 p792a2) (+ p88a0 p88a2)) :named weak_SD-strategyproofness_2598))
; This manipulation was obtained from p88:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 3 > 0 ~ 1 > 2
; To:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 3 > 0 ~ 1 > 2
; 1 agent : 2 > 0 > 1 > 3
; By replacing voter 0 ~ 2 > 1 ~ 3 with 2 > 0 > 1 > 3
; The manipulated profile in canonical form is p792:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 3 > 0 ~ 1 > 2
; 1 agent : 2 > 0 > 1 > 3
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< p625a2 p591a0) (< (+ p625a2 p625a1) (+ p591a0 p591a2)) (and (= p625a2 p591a0) (= (+ p625a2 p625a1) (+ p591a0 p591a2)))) :named weak_SD-strategyproofness_3113))
; This manipulation was obtained from p591:
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 1 > 0 > 2 ~ 3
; 1 agent : 0 > 2 > 1 ~ 3
; 1 agent : 3 > 2 > 0 ~ 1
; To:
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 1 > 0 > 2 ~ 3
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 0 > 2 ~ 3 > 1
; By replacing voter 0 > 2 > 1 ~ 3 with 0 > 2 ~ 3 > 1
; The manipulated profile in canonical form is p625:
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 2 > 0 ~ 1 > 3
; 1 agent : 0 > 1 > 2 ~ 3
; It can be obtained via isomorphism: {0=2, 1=3, 2=1, 3=0}
(assert (! (or (< p608a2 p285a1) (< (+ p608a3 p608a2 p608a0) (+ p285a0 p285a1 p285a3)) (and (= p608a2 p285a1) (= (+ p608a3 p608a2 p608a0) (+ p285a0 p285a1 p285a3)))) :named weak_SD-strategyproofness_3244))
; This manipulation was obtained from p285:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 > 2 > 3 > 1
; 1 agent : 1 > 0 ~ 3 > 2
; 1 agent : 2 > 3 > 0 ~ 1
; To:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 > 2 > 3 > 1
; 1 agent : 2 > 3 > 0 ~ 1
; 1 agent : 1 > 3 > 0 ~ 2
; By replacing voter 1 > 0 ~ 3 > 2 with 1 > 3 > 0 ~ 2
; The manipulated profile in canonical form is p608:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 3 > 1 > 0 > 2
; 1 agent : 2 > 0 > 1 ~ 3
; 1 agent : 1 > 0 > 2 ~ 3
; It can be obtained via isomorphism: {0=3, 1=2, 2=1, 3=0}
(assert (! (or (< p0a3 p44a3) (< (+ p0a0 p0a1 p0a3) (+ p44a0 p44a1 p44a3)) (and (= p0a3 p44a3) (= (+ p0a0 p0a1 p0a3) (+ p44a0 p44a1 p44a3)))) :named weak_SD-strategyproofness_5430))
; This manipulation was obtained from p44:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 3 > 0 ~ 1 > 2
; To:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; By replacing voter 3 > 0 ~ 1 > 2 with 1 ~ 3 > 0 > 2
; The manipulated profile in canonical form is p0:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< (+ p248a3 p248a1) (+ p48a1 p48a3)) (< (+ p248a2 p248a3 p248a1) (+ p48a0 p48a1 p48a3)) (and (= (+ p248a3 p248a1) (+ p48a1 p48a3)) (= (+ p248a2 p248a3 p248a1) (+ p48a0 p48a1 p48a3)))) :named weak_SD-strategyproofness_5438))
; This manipulation was obtained from p48:
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 2 > 3 > 0 ~ 1
; 1 agent : 0 ~ 1 > 2 > 3
; To:
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 2 > 3 > 0 ~ 1
; 1 agent : 0 ~ 1 > 2 > 3
; 1 agent : 1 ~ 3 > 2 > 0
; By replacing voter 1 ~ 3 > 0 > 2 with 1 ~ 3 > 2 > 0
; The manipulated profile in canonical form is p248:
; 1 agent : 2 ~ 3 > 0 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 0 ~ 2 > 1 > 3
; It can be obtained via isomorphism: {0=2, 1=3, 2=0, 3=1}
(assert (! (or (< p409a2 p624a2) (< (+ p409a0 p409a1 p409a2) (+ p624a0 p624a1 p624a2)) (and (= p409a2 p624a2) (= (+ p409a0 p409a1 p409a2) (+ p624a0 p624a1 p624a2)))) :named weak_SD-strategyproofness_5662))
; This manipulation was obtained from p624:
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 2 > 0 ~ 1 > 3
; 1 agent : 0 ~ 1 > 3 > 2
; To:
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 0 ~ 1 > 3 > 2
; 1 agent : 0 ~ 1 ~ 2 > 3
; By replacing voter 2 > 0 ~ 1 > 3 with 0 ~ 1 ~ 2 > 3
; The manipulated profile in canonical form is p409:
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 0 ~ 1 > 3 > 2
; 1 agent : 0 ~ 1 ~ 2 > 3
; 1 agent : 3 > 2 > 0 ~ 1
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< (+ p625a0 p625a1) (+ p624a0 p624a1)) (< (+ p625a0 p625a1 p625a3) (+ p624a0 p624a1 p624a3)) (and (= (+ p625a0 p625a1) (+ p624a0 p624a1)) (= (+ p625a0 p625a1 p625a3) (+ p624a0 p624a1 p624a3)))) :named weak_SD-strategyproofness_5675))
; This manipulation was obtained from p624:
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 2 > 0 ~ 1 > 3
; 1 agent : 0 ~ 1 > 3 > 2
; To:
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 2 > 0 ~ 1 > 3
; 1 agent : 0 > 1 > 2 ~ 3
; By replacing voter 0 ~ 1 > 3 > 2 with 0 > 1 > 2 ~ 3
; The manipulated profile in canonical form is p625:
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 2 > 0 ~ 1 > 3
; 1 agent : 0 > 1 > 2 ~ 3
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< p496a2 p625a2) (< (+ p496a0 p496a1 p496a2) (+ p625a0 p625a1 p625a2)) (and (= p496a2 p625a2) (= (+ p496a0 p496a1 p496a2) (+ p625a0 p625a1 p625a2)))) :named weak_SD-strategyproofness_5996))
; This manipulation was obtained from p625:
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 2 > 0 ~ 1 > 3
; 1 agent : 0 > 1 > 2 ~ 3
; To:
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 0 ~ 1 ~ 2 > 3
; By replacing voter 2 > 0 ~ 1 > 3 with 0 ~ 1 ~ 2 > 3
; The manipulated profile in canonical form is p496:
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 0 ~ 1 ~ 2 > 3
; 1 agent : 3 > 2 > 0 ~ 1
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (<= (+ p48a0 p48a1 p48a3) (+ p409a0 p409a1 p409a2)) :named weak_SD-strategyproofness_6906))
; This manipulation was obtained from p409:
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 0 ~ 1 > 3 > 2
; 1 agent : 0 ~ 1 ~ 2 > 3
; 1 agent : 3 > 2 > 0 ~ 1
; To:
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 0 ~ 1 > 3 > 2
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 1 ~ 2 > 0 > 3
; By replacing voter 0 ~ 1 ~ 2 > 3 with 1 ~ 2 > 0 > 3
; The manipulated profile in canonical form is p48:
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 2 > 3 > 0 ~ 1
; 1 agent : 0 ~ 1 > 2 > 3
; It can be obtained via isomorphism: {0=0, 1=1, 2=3, 3=2}
(assert (! (or (< p249a0 p641a3) (< (+ p249a3 p249a1 p249a0) (+ p641a0 p641a1 p641a3)) (and (= p249a0 p641a3) (= (+ p249a3 p249a1 p249a0) (+ p641a0 p641a1 p641a3)))) :named weak_SD-strategyproofness_6975))
; This manipulation was obtained from p641:
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 3 > 0 ~ 1 > 2
; 1 agent : 0 ~ 1 > 3 > 2
; To:
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 0 ~ 1 > 3 > 2
; 1 agent : 3 > 1 > 0 ~ 2
; By replacing voter 3 > 0 ~ 1 > 2 with 3 > 1 > 0 ~ 2
; The manipulated profile in canonical form is p249:
; 1 agent : 2 ~ 3 > 0 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 0 > 2 > 1 ~ 3
; It can be obtained via isomorphism: {0=3, 1=1, 2=2, 3=0}
(assert (! (or (< (+ p642a0 p642a1) (+ p641a0 p641a1)) (< (+ p642a0 p642a1 p642a3) (+ p641a0 p641a1 p641a3)) (and (= (+ p642a0 p642a1) (+ p641a0 p641a1)) (= (+ p642a0 p642a1 p642a3) (+ p641a0 p641a1 p641a3)))) :named weak_SD-strategyproofness_6983))
; This manipulation was obtained from p641:
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 3 > 0 ~ 1 > 2
; 1 agent : 0 ~ 1 > 3 > 2
; To:
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 3 > 0 ~ 1 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; By replacing voter 0 ~ 1 > 3 > 2 with 0 > 1 > 2 ~ 3
; The manipulated profile in canonical form is p642:
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 3 > 0 ~ 1 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< p55a0 p496a0) (< (+ p55a0 p55a1) (+ p496a0 p496a1)) (and (= p55a0 p496a0) (= (+ p55a0 p55a1) (+ p496a0 p496a1)))) :named weak_SD-strategyproofness_7188))
; This manipulation was obtained from p496:
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 0 ~ 1 ~ 2 > 3
; 1 agent : 3 > 2 > 0 ~ 1
; To:
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 0 ~ 1 ~ 2 > 3
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 0 ~ 1 > 2 ~ 3
; By replacing voter 0 > 1 > 2 ~ 3 with 0 ~ 1 > 2 ~ 3
; The manipulated profile in canonical form is p55:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 0 ~ 1 ~ 2 > 3
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< p12a3 p642a3) (< (+ p12a0 p12a1 p12a3) (+ p642a0 p642a1 p642a3)) (and (= p12a3 p642a3) (= (+ p12a0 p12a1 p12a3) (+ p642a0 p642a1 p642a3)))) :named weak_SD-strategyproofness_7267))
; This manipulation was obtained from p642:
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 3 > 0 ~ 1 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; To:
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 1 ~ 3 > 0 > 2
; By replacing voter 3 > 0 ~ 1 > 2 with 1 ~ 3 > 0 > 2
; The manipulated profile in canonical form is p12:
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 3 > 2 > 0 ~ 1
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (<= (+ p6a0 p6a1 p6a3) (+ p85a0 p85a1 p85a3)) :named weak_SD-strategyproofness_7954))
; This manipulation was obtained from p85:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 0 ~ 1 ~ 3 > 2
; To:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 1 ~ 3 > 0 > 2
; By replacing voter 0 ~ 1 ~ 3 > 2 with 1 ~ 3 > 0 > 2
; The manipulated profile in canonical form is p6:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 2 > 1 ~ 3
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< p792a3 p130a2) (< (+ p792a1 p792a3) (+ p130a0 p130a2)) (and (= p792a3 p130a2) (= (+ p792a1 p792a3) (+ p130a0 p130a2)))) :named weak_SD-strategyproofness_8538))
; This manipulation was obtained from p130:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 3 > 1 > 0 > 2
; 1 agent : 2 > 0 > 1 ~ 3
; To:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 3 > 1 > 0 > 2
; 1 agent : 2 > 0 ~ 1 > 3
; By replacing voter 2 > 0 > 1 ~ 3 with 2 > 0 ~ 1 > 3
; The manipulated profile in canonical form is p792:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 3 > 0 ~ 1 > 2
; 1 agent : 2 > 0 > 1 > 3
; It can be obtained via isomorphism: {0=1, 1=0, 2=3, 3=2}
(assert (! (<= (+ p0a0 p0a1 p0a3) (+ p42a0 p42a1 p42a3)) :named weak_SD-strategyproofness_10027))
; This manipulation was obtained from p42:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 0 ~ 1 ~ 3 > 2
; To:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; By replacing voter 0 ~ 1 ~ 3 > 2 with 1 ~ 3 > 0 > 2
; The manipulated profile in canonical form is p0:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< p285a1 p608a2) (< (+ p285a3 p285a1) (+ p608a0 p608a2)) (and (= p285a1 p608a2) (= (+ p285a3 p285a1) (+ p608a0 p608a2)))) :named weak_SD-strategyproofness_10865))
; This manipulation was obtained from p608:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 3 > 1 > 0 > 2
; 1 agent : 2 > 0 > 1 ~ 3
; 1 agent : 1 > 0 > 2 ~ 3
; To:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 3 > 1 > 0 > 2
; 1 agent : 1 > 0 > 2 ~ 3
; 1 agent : 2 > 0 ~ 3 > 1
; By replacing voter 2 > 0 > 1 ~ 3 with 2 > 0 ~ 3 > 1
; The manipulated profile in canonical form is p285:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 > 2 > 3 > 1
; 1 agent : 1 > 0 ~ 3 > 2
; 1 agent : 2 > 3 > 0 ~ 1
; It can be obtained via isomorphism: {0=3, 1=2, 2=1, 3=0}
(assert (! (or (< p3a0 p22a0) (< (+ p3a0 p3a2) (+ p22a0 p22a2)) (and (= p3a0 p22a0) (= (+ p3a0 p3a2) (+ p22a0 p22a2)))) :named weak_SD-strategyproofness_11265))
; This manipulation was obtained from p22:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 0 > 2 > 1 ~ 3
; To:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 0 ~ 2 > 3 > 1
; By replacing voter 0 > 2 > 1 ~ 3 with 0 ~ 2 > 3 > 1
; The manipulated profile in canonical form is p3:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< p130a3 p335a0) (< (+ p130a3 p130a1) (+ p335a0 p335a1)) (and (= p130a3 p335a0) (= (+ p130a3 p130a1) (+ p335a0 p335a1)))) :named weak_SD-strategyproofness_11817))
; This manipulation was obtained from p335:
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 1 ~ 3 > 0 ~ 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 2 > 3 > 0 ~ 1
; To:
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 1 ~ 3 > 0 ~ 2
; 1 agent : 2 > 3 > 0 ~ 1
; 1 agent : 0 > 1 > 3 > 2
; By replacing voter 0 > 1 > 2 ~ 3 with 0 > 1 > 3 > 2
; The manipulated profile in canonical form is p130:
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 3 > 1 > 0 > 2
; 1 agent : 2 > 0 > 1 ~ 3
; It can be obtained via isomorphism: {0=3, 1=1, 2=2, 3=0}
(assert (! (or (< p80a0 p114a0) (< (+ p80a0 p80a1) (+ p114a0 p114a1)) (< (+ p80a0 p80a1 p80a3) (+ p114a0 p114a1 p114a3)) (and (= p80a0 p114a0) (= (+ p80a0 p80a1) (+ p114a0 p114a1)) (= (+ p80a0 p80a1 p80a3) (+ p114a0 p114a1 p114a3)))) :named weak_SD-strategyproofness_14806))
; This manipulation was obtained from p114:
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 2 ~ 3 > 0 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 3 > 2
; To:
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 2 ~ 3 > 0 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 1 > 2 ~ 3
; By replacing voter 0 > 1 > 3 > 2 with 0 ~ 1 > 2 ~ 3
; The manipulated profile in canonical form is p80:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 2 ~ 3 > 0 > 1
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (<= (+ p114a0 p114a1) (+ p80a0 p80a1)) :named weak_SD-strategyproofness_15215))
; This manipulation was obtained from p80:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 2 ~ 3 > 0 > 1
; To:
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 2 ~ 3 > 0 > 1
; 1 agent : 0 > 1 > 3 > 2
; By replacing voter 0 ~ 1 > 2 ~ 3 with 0 > 1 > 3 > 2
; The manipulated profile in canonical form is p114:
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 2 ~ 3 > 0 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 3 > 2
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< p127a2 p654a3) (< (+ p127a3 p127a2) (+ p654a2 p654a3)) (and (= p127a2 p654a3) (= (+ p127a3 p127a2) (+ p654a2 p654a3)))) :named weak_SD-strategyproofness_16507))
; This manipulation was obtained from p654:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 0 ~ 1 ~ 2 > 3
; 1 agent : 0 > 3 > 2 > 1
; To:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 1 ~ 2 > 3
; 1 agent : 0 > 3 > 2 > 1
; 1 agent : 2 ~ 3 > 0 ~ 1
; By replacing voter 3 > 2 > 0 ~ 1 with 2 ~ 3 > 0 ~ 1
; The manipulated profile in canonical form is p127:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 > 2 > 3 > 1
; 1 agent : 0 ~ 1 ~ 3 > 2
; It can be obtained via isomorphism: {0=0, 1=1, 2=3, 3=2}
(assert (! (<= (+ p285a0 p285a1 p285a3) (+ p654a0 p654a1 p654a2)) :named weak_SD-strategyproofness_16520))
; This manipulation was obtained from p654:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 0 ~ 1 ~ 2 > 3
; 1 agent : 0 > 3 > 2 > 1
; To:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 0 > 3 > 2 > 1
; 1 agent : 1 > 0 ~ 2 > 3
; By replacing voter 0 ~ 1 ~ 2 > 3 with 1 > 0 ~ 2 > 3
; The manipulated profile in canonical form is p285:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 > 2 > 3 > 1
; 1 agent : 1 > 0 ~ 3 > 2
; 1 agent : 2 > 3 > 0 ~ 1
; It can be obtained via isomorphism: {0=0, 1=1, 2=3, 3=2}
(assert (! (or (< p55a0 p654a0) (< (+ p55a0 p55a3) (+ p654a0 p654a3)) (< (+ p55a0 p55a2 p55a3) (+ p654a0 p654a2 p654a3)) (and (= p55a0 p654a0) (= (+ p55a0 p55a3) (+ p654a0 p654a3)) (= (+ p55a0 p55a2 p55a3) (+ p654a0 p654a2 p654a3)))) :named weak_SD-strategyproofness_16523))
; This manipulation was obtained from p654:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 0 ~ 1 ~ 2 > 3
; 1 agent : 0 > 3 > 2 > 1
; To:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 0 ~ 1 ~ 2 > 3
; 1 agent : 0 ~ 3 > 2 > 1
; By replacing voter 0 > 3 > 2 > 1 with 0 ~ 3 > 2 > 1
; The manipulated profile in canonical form is p55:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 0 ~ 1 ~ 2 > 3
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< (+ p48a2 p48a3) (+ p135a0 p135a2)) (< (+ p48a2 p48a3 p48a1) (+ p135a0 p135a2 p135a3)) (and (= (+ p48a2 p48a3) (+ p135a0 p135a2)) (= (+ p48a2 p48a3 p48a1) (+ p135a0 p135a2 p135a3)))) :named weak_SD-strategyproofness_18224))
; This manipulation was obtained from p135:
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 1 > 2 > 3
; 1 agent : 2 ~ 3 > 1 > 0
; To:
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 1 > 2 > 3
; 1 agent : 2 ~ 3 > 1 > 0
; 1 agent : 0 > 2 > 1 ~ 3
; By replacing voter 0 ~ 2 > 3 > 1 with 0 > 2 > 1 ~ 3
; The manipulated profile in canonical form is p48:
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 2 > 3 > 0 ~ 1
; 1 agent : 0 ~ 1 > 2 > 3
; It can be obtained via isomorphism: {0=2, 1=0, 2=3, 3=1}
(assert (! (or (< (+ p12a2 p12a3) (+ p9a2 p9a3)) (< (+ p12a0 p12a2 p12a3) (+ p9a0 p9a2 p9a3)) (and (= (+ p12a2 p12a3) (+ p9a2 p9a3)) (= (+ p12a0 p12a2 p12a3) (+ p9a0 p9a2 p9a3)))) :named weak_SD-strategyproofness_18352))
; This manipulation was obtained from p9:
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 > 1
; To:
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 3 > 2 > 0 ~ 1
; By replacing voter 2 ~ 3 > 0 > 1 with 3 > 2 > 0 ~ 1
; The manipulated profile in canonical form is p12:
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 3 > 2 > 0 ~ 1
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< (+ p335a0 p335a2) (+ p377a1 p377a3)) (< (+ p335a1 p335a0 p335a2) (+ p377a0 p377a1 p377a3)) (and (= (+ p335a0 p335a2) (+ p377a1 p377a3)) (= (+ p335a1 p335a0 p335a2) (+ p377a0 p377a1 p377a3)))) :named weak_SD-strategyproofness_19248))
; This manipulation was obtained from p377:
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 1 > 0 > 2 ~ 3
; To:
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 1 > 0 > 2 ~ 3
; 1 agent : 1 ~ 3 > 0 ~ 2
; By replacing voter 1 ~ 3 > 0 > 2 with 1 ~ 3 > 0 ~ 2
; The manipulated profile in canonical form is p335:
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 1 ~ 3 > 0 ~ 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 2 > 3 > 0 ~ 1
; It can be obtained via isomorphism: {0=1, 1=0, 2=3, 3=2}
(assert (! (<= (+ p591a0 p591a2) (+ p377a0 p377a2)) :named weak_SD-strategyproofness_19267))
; This manipulation was obtained from p377:
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 1 > 0 > 2 ~ 3
; To:
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 1 > 0 > 2 ~ 3
; 1 agent : 0 > 2 > 1 ~ 3
; By replacing voter 0 ~ 2 > 1 ~ 3 with 0 > 2 > 1 ~ 3
; The manipulated profile in canonical form is p591:
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 1 > 0 > 2 ~ 3
; 1 agent : 0 > 2 > 1 ~ 3
; 1 agent : 3 > 2 > 0 ~ 1
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< p333a0 p175a3) (< (+ p333a3 p333a1 p333a0) (+ p175a0 p175a1 p175a3)) (and (= p333a0 p175a3) (= (+ p333a3 p333a1 p333a0) (+ p175a0 p175a1 p175a3)))) :named weak_SD-strategyproofness_20441))
; This manipulation was obtained from p175:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 3 > 0 ~ 1 > 2
; 1 agent : 3 > 2 > 0 ~ 1
; To:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 3 > 1 > 0 ~ 2
; By replacing voter 3 > 0 ~ 1 > 2 with 3 > 1 > 0 ~ 2
; The manipulated profile in canonical form is p333:
; 1 agent : 1 ~ 3 > 0 ~ 2
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 0 > 2 > 1 ~ 3
; It can be obtained via isomorphism: {0=3, 1=1, 2=2, 3=0}
(assert (! (or (< p9a0 p249a0) (< (+ p9a0 p9a2) (+ p249a0 p249a1)) (and (= p9a0 p249a0) (= (+ p9a0 p9a2) (+ p249a0 p249a1)))) :named weak_SD-strategyproofness_21574))
; This manipulation was obtained from p249:
; 1 agent : 2 ~ 3 > 0 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 0 > 2 > 1 ~ 3
; To:
; 1 agent : 2 ~ 3 > 0 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 2 > 1 ~ 3
; 1 agent : 0 ~ 1 > 3 > 2
; By replacing voter 0 > 1 > 2 ~ 3 with 0 ~ 1 > 3 > 2
; The manipulated profile in canonical form is p9:
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 > 1
; It can be obtained via isomorphism: {0=0, 1=2, 2=1, 3=3}
(assert (! (<= (+ p58a0 p58a3) (+ p174a0 p174a3)) :named weak_SD-strategyproofness_23507))
; This manipulation was obtained from p174:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 3 > 1 ~ 2
; 1 agent : 2 > 0 ~ 1 > 3
; 1 agent : 3 > 2 > 0 ~ 1
; To:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 > 0 ~ 1 > 3
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 0 ~ 3 > 2 > 1
; By replacing voter 0 ~ 3 > 1 ~ 2 with 0 ~ 3 > 2 > 1
; The manipulated profile in canonical form is p58:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 2 > 0 ~ 1 > 3
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< p573a2 p174a2) (< (+ p573a0 p573a1 p573a2) (+ p174a0 p174a1 p174a2)) (and (= p573a2 p174a2) (= (+ p573a0 p573a1 p573a2) (+ p174a0 p174a1 p174a2)))) :named weak_SD-strategyproofness_23514))
; This manipulation was obtained from p174:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 3 > 1 ~ 2
; 1 agent : 2 > 0 ~ 1 > 3
; 1 agent : 3 > 2 > 0 ~ 1
; To:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 3 > 1 ~ 2
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 0 ~ 1 ~ 2 > 3
; By replacing voter 2 > 0 ~ 1 > 3 with 0 ~ 1 ~ 2 > 3
; The manipulated profile in canonical form is p573:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 3 > 1 ~ 2
; 1 agent : 0 ~ 1 ~ 2 > 3
; 1 agent : 3 > 2 > 0 ~ 1
; It can be obtained via isomorphism: {0=0, 1=1, 2=2, 3=3}
(assert (! (or (< p175a2 p174a3) (< (+ p175a3 p175a2) (+ p174a2 p174a3)) (and (= p175a2 p174a3) (= (+ p175a3 p175a2) (+ p174a2 p174a3)))) :named weak_SD-strategyproofness_23528))
; This manipulation was obtained from p174:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 3 > 1 ~ 2
; 1 agent : 2 > 0 ~ 1 > 3
; 1 agent : 3 > 2 > 0 ~ 1
; To:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 3 > 1 ~ 2
; 1 agent : 2 > 0 ~ 1 > 3
; 1 agent : 2 > 3 > 0 ~ 1
; By replacing voter 3 > 2 > 0 ~ 1 with 2 > 3 > 0 ~ 1
; The manipulated profile in canonical form is p175:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 3 > 0 ~ 1 > 2
; 1 agent : 3 > 2 > 0 ~ 1
; It can be obtained via isomorphism: {0=0, 1=1, 2=3, 3=2}
; (echo "Orbit condition (part of neutrality)")
(assert (! (= p0a2 p0a1) :named orbit_p0a2_p0a1_24278))
; Orbit [1, 2] for profile p0:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
(assert (! (= p333a2 p333a1) :named orbit_p333a2_p333a1_24352))
; Orbit [1, 2] for profile p333:
; 1 agent : 1 ~ 3 > 0 ~ 2
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 0 > 2 > 1 ~ 3
(assert (! (= p80a2 p80a1) :named orbit_p80a2_p80a1_24355))
; Orbit [1, 2] for profile p80:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 2 ~ 3 > 0 > 1
(assert (! (= p249a2 p249a1) :named orbit_p249a2_p249a1_24356))
; Orbit [1, 2] for profile p249:
; 1 agent : 2 ~ 3 > 0 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 0 > 2 > 1 ~ 3
(assert (! (= p12a2 p12a1) :named orbit_p12a2_p12a1_24360))
; Orbit [1, 2] for profile p12:
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 3 > 2 > 0 ~ 1
(assert (! (= p12a3 p12a0) :named orbit_p12a3_p12a0_24361))
; Orbit [0, 3] for profile p12:
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 3 > 2 > 0 ~ 1
(assert (! (= p335a3 p335a1) :named orbit_p335a3_p335a1_24390))
; Orbit [1, 3] for profile p335:
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 1 ~ 3 > 0 ~ 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 2 > 3 > 0 ~ 1
(assert (! (= p335a2 p335a0) :named orbit_p335a2_p335a0_24391))
; Orbit [0, 2] for profile p335:
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 1 ~ 3 > 0 ~ 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 2 > 3 > 0 ~ 1
(assert (! (= p548a2 p548a1) :named orbit_p548a2_p548a1_24404))
; Orbit [1, 2] for profile p548:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 3 > 0 ~ 1 > 2
; 1 agent : 0 > 2 ~ 3 > 1
(assert (! (= p548a3 p548a0) :named orbit_p548a3_p548a0_24405))
; Orbit [0, 3] for profile p548:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 3 > 0 ~ 1 > 2
; 1 agent : 0 > 2 ~ 3 > 1
(assert (! (= p135a1 p135a0) :named orbit_p135a1_p135a0_24417))
; Orbit [0, 1, 2, 3] for profile p135:
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 1 > 2 > 3
; 1 agent : 2 ~ 3 > 1 > 0
(assert (! (= p135a2 p135a0) :named orbit_p135a2_p135a0_24418))
; Orbit [0, 1, 2, 3] for profile p135:
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 1 > 2 > 3
; 1 agent : 2 ~ 3 > 1 > 0
(assert (! (= p135a3 p135a0) :named orbit_p135a3_p135a0_24420))
; Orbit [0, 1, 2, 3] for profile p135:
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 1 > 2 > 3
; 1 agent : 2 ~ 3 > 1 > 0
; (echo "SD-efficiency")
(assert (! (= p178a1 0.0) :named sdEfficiency_24649))
; Inefficient support [1] at profile p178:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 3 > 0 ~ 1 > 2
; 1 agent : 2 > 0 > 1 ~ 3
(assert (! (= p55a1 0.0) :named sdEfficiency_24857))
; Inefficient support [1] at profile p55:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 0 ~ 1 ~ 2 > 3
(assert (! (or (= p0a1 0.0) (= p0a2 0.0)) :named sdEfficiency_24868))
; Inefficient support [1, 2] at profile p0:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
(assert (! (= p792a1 0.0) :named sdEfficiency_24914))
; Inefficient support [1] at profile p792:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 3 > 0 ~ 1 > 2
; 1 agent : 2 > 0 > 1 > 3
(assert (! (= p127a1 0.0) :named sdEfficiency_25033))
; Inefficient support [1] at profile p127:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 > 2 > 3 > 1
; 1 agent : 0 ~ 1 ~ 3 > 2
(assert (! (= p88a1 0.0) :named sdEfficiency_25040))
; Inefficient support [1] at profile p88:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 3 > 0 ~ 1 > 2
(assert (! (= p573a1 0.0) :named sdEfficiency_25042))
; Inefficient support [1] at profile p573:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 3 > 1 ~ 2
; 1 agent : 0 ~ 1 ~ 2 > 3
; 1 agent : 3 > 2 > 0 ~ 1
(assert (! (or (= p6a1 0.0) (= p6a2 0.0)) :named sdEfficiency_25155))
; Inefficient support [1, 2] at profile p6:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 2 > 1 ~ 3
(assert (! (or (= p333a1 0.0) (= p333a2 0.0)) :named sdEfficiency_25275))
; Inefficient support [1, 2] at profile p333:
; 1 agent : 1 ~ 3 > 0 ~ 2
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 0 > 2 > 1 ~ 3
(assert (! (or (= p80a1 0.0) (= p80a2 0.0)) :named sdEfficiency_25297))
; Inefficient support [1, 2] at profile p80:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 ~ 2 > 1 ~ 3
; 1 agent : 2 ~ 3 > 0 > 1
(assert (! (or (= p249a1 0.0) (= p249a2 0.0)) :named sdEfficiency_25316))
; Inefficient support [1, 2] at profile p249:
; 1 agent : 2 ~ 3 > 0 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 0 > 2 > 1 ~ 3
(assert (! (or (= p12a1 0.0) (= p12a2 0.0)) :named sdEfficiency_25331))
; Inefficient support [1, 2] at profile p12:
; 1 agent : 0 ~ 2 > 3 > 1
; 1 agent : 1 ~ 3 > 0 > 2
; 1 agent : 0 > 1 > 2 ~ 3
; 1 agent : 3 > 2 > 0 ~ 1
(assert (! (= p548a1 0.0) :named sdEfficiency_25917))
; Inefficient support [1] at profile p548:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 2 ~ 3 > 0 ~ 1
; 1 agent : 3 > 0 ~ 1 > 2
; 1 agent : 0 > 2 ~ 3 > 1
(assert (! (= p58a1 0.0) :named sdEfficiency_26018))
; Inefficient support [1] at profile p58:
; 1 agent : 0 ~ 1 > 2 ~ 3
; 1 agent : 0 ~ 3 > 2 > 1
; 1 agent : 3 > 2 > 0 ~ 1
; 1 agent : 2 > 0 ~ 1 > 3
(check-sat)
(get-proof)
