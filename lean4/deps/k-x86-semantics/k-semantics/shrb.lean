def shrb1 : instruction :=
  definst "shrb" $ do
    pattern fun cl (v_2883 : reg (bv 8)) => do
      v_5492 <- getRegister rcx;
      v_5494 <- eval (bv_and (extract v_5492 56 64) (expression.bv_nat 8 31));
      v_5495 <- eval (uge v_5494 (expression.bv_nat 8 8));
      v_5498 <- eval (eq v_5494 (expression.bv_nat 8 0));
      v_5499 <- eval (notBool_ v_5498);
      v_5500 <- getRegister v_2883;
      v_5504 <- eval (lshr (concat v_5500 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 1 0) v_5494)));
      v_5508 <- getRegister cf;
      v_5516 <- eval (eq (extract v_5504 0 1) (expression.bv_nat 1 1));
      v_5518 <- getRegister sf;
      v_5523 <- eval (bit_and v_5499 undef);
      v_5524 <- getRegister af;
      v_5529 <- eval (extract v_5504 0 8);
      v_5532 <- getRegister zf;
      v_5565 <- getRegister pf;
      v_5570 <- eval (eq v_5494 (expression.bv_nat 8 1));
      v_5575 <- getRegister of;
      setRegister (lhs.of_reg v_2883) v_5529;
      setRegister of (mux (bit_or (bit_and v_5570 (eq (extract v_5500 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_5570) (bit_or v_5523 (bit_and v_5498 (eq v_5575 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_5499 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_5504 7 8) (expression.bv_nat 1 1)) (eq (extract v_5504 6 7) (expression.bv_nat 1 1)))) (eq (extract v_5504 5 6) (expression.bv_nat 1 1)))) (eq (extract v_5504 4 5) (expression.bv_nat 1 1)))) (eq (extract v_5504 3 4) (expression.bv_nat 1 1)))) (eq (extract v_5504 2 3) (expression.bv_nat 1 1)))) (eq (extract v_5504 1 2) (expression.bv_nat 1 1)))) v_5516)) (bit_and v_5498 (eq v_5565 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_5499 (eq v_5529 (expression.bv_nat 8 0))) (bit_and v_5498 (eq v_5532 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_5523 (bit_and v_5498 (eq v_5524 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_5499 v_5516) (bit_and v_5498 (eq v_5518 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5495 undef) (bit_and (notBool_ v_5495) (bit_or (bit_and v_5499 (eq (extract v_5504 8 9) (expression.bv_nat 1 1))) (bit_and v_5498 (eq v_5508 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2886 : imm int) (v_2888 : reg (bv 8)) => do
      v_5590 <- eval (bv_and (handleImmediateWithSignExtend v_2886 8 8) (expression.bv_nat 8 31));
      v_5591 <- eval (uge v_5590 (expression.bv_nat 8 8));
      v_5594 <- eval (eq v_5590 (expression.bv_nat 8 0));
      v_5595 <- eval (notBool_ v_5594);
      v_5596 <- getRegister v_2888;
      v_5600 <- eval (lshr (concat v_5596 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 1 0) v_5590)));
      v_5604 <- getRegister cf;
      v_5612 <- eval (eq (extract v_5600 0 1) (expression.bv_nat 1 1));
      v_5614 <- getRegister sf;
      v_5619 <- eval (bit_and v_5595 undef);
      v_5620 <- getRegister af;
      v_5625 <- eval (extract v_5600 0 8);
      v_5628 <- getRegister zf;
      v_5661 <- getRegister pf;
      v_5666 <- eval (eq v_5590 (expression.bv_nat 8 1));
      v_5671 <- getRegister of;
      setRegister (lhs.of_reg v_2888) v_5625;
      setRegister of (mux (bit_or (bit_and v_5666 (eq (extract v_5596 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_5666) (bit_or v_5619 (bit_and v_5594 (eq v_5671 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_5595 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_5600 7 8) (expression.bv_nat 1 1)) (eq (extract v_5600 6 7) (expression.bv_nat 1 1)))) (eq (extract v_5600 5 6) (expression.bv_nat 1 1)))) (eq (extract v_5600 4 5) (expression.bv_nat 1 1)))) (eq (extract v_5600 3 4) (expression.bv_nat 1 1)))) (eq (extract v_5600 2 3) (expression.bv_nat 1 1)))) (eq (extract v_5600 1 2) (expression.bv_nat 1 1)))) v_5612)) (bit_and v_5594 (eq v_5661 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_5595 (eq v_5625 (expression.bv_nat 8 0))) (bit_and v_5594 (eq v_5628 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_5619 (bit_and v_5594 (eq v_5620 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_5595 v_5612) (bit_and v_5594 (eq v_5614 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5591 undef) (bit_and (notBool_ v_5591) (bit_or (bit_and v_5595 (eq (extract v_5600 8 9) (expression.bv_nat 1 1))) (bit_and v_5594 (eq v_5604 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2895 : reg (bv 8)) => do
      v_5687 <- getRegister v_2895;
      v_5689 <- eval (lshr (concat v_5687 (expression.bv_nat 1 0)) 1);
      v_5692 <- eval (extract v_5689 0 8);
      setRegister (lhs.of_reg v_2895) v_5692;
      setRegister of (extract v_5687 0 1);
      setRegister pf (parityFlag v_5692);
      setRegister zf (zeroFlag v_5692);
      setRegister af undef;
      setRegister sf (extract v_5689 0 1);
      setRegister cf (extract v_5689 8 9);
      pure ()
    pat_end;
    pattern fun (v_2891 : reg (bv 8)) => do
      v_7896 <- getRegister v_2891;
      v_7898 <- eval (lshr (concat v_7896 (expression.bv_nat 1 0)) 1);
      v_7905 <- eval (extract v_7898 0 8);
      setRegister (lhs.of_reg v_2891) v_7905;
      setRegister of (mux (eq (extract v_7896 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_7905);
      setRegister zf (zeroFlag v_7905);
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (eq (extract v_7898 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_7898 8 9) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2891 : reg (bv 8)) => do
      v_7918 <- getRegister v_2891;
      v_7920 <- eval (lshr (concat v_7918 (expression.bv_nat 1 0)) 1);
      v_7923 <- eval (extract v_7920 0 8);
      setRegister (lhs.of_reg v_2891) v_7923;
      setRegister of (extract v_7918 0 1);
      setRegister pf (parityFlag v_7923);
      setRegister zf (zeroFlag v_7923);
      setRegister af undef;
      setRegister sf (extract v_7920 0 1);
      setRegister cf (extract v_7920 8 9);
      pure ()
    pat_end;
    pattern fun cl (v_2869 : Mem) => do
      v_11871 <- evaluateAddress v_2869;
      v_11872 <- load v_11871 1;
      v_11874 <- getRegister rcx;
      v_11876 <- eval (bv_and (extract v_11874 56 64) (expression.bv_nat 8 31));
      v_11879 <- eval (lshr (concat v_11872 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 1 0) v_11876)));
      v_11880 <- eval (extract v_11879 0 8);
      store v_11871 v_11880 1;
      v_11882 <- eval (uge v_11876 (expression.bv_nat 8 8));
      v_11885 <- eval (eq v_11876 (expression.bv_nat 8 0));
      v_11886 <- eval (notBool_ v_11885);
      v_11890 <- getRegister cf;
      v_11898 <- eval (eq (extract v_11879 0 1) (expression.bv_nat 1 1));
      v_11900 <- getRegister sf;
      v_11907 <- getRegister zf;
      v_11912 <- eval (bit_and v_11886 undef);
      v_11913 <- getRegister af;
      v_11946 <- getRegister pf;
      v_11951 <- eval (eq v_11876 (expression.bv_nat 8 1));
      v_11956 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_11951 (eq (extract v_11872 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_11951) (bit_or v_11912 (bit_and v_11885 (eq v_11956 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_11886 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_11879 7 8) (expression.bv_nat 1 1)) (eq (extract v_11879 6 7) (expression.bv_nat 1 1)))) (eq (extract v_11879 5 6) (expression.bv_nat 1 1)))) (eq (extract v_11879 4 5) (expression.bv_nat 1 1)))) (eq (extract v_11879 3 4) (expression.bv_nat 1 1)))) (eq (extract v_11879 2 3) (expression.bv_nat 1 1)))) (eq (extract v_11879 1 2) (expression.bv_nat 1 1)))) v_11898)) (bit_and v_11885 (eq v_11946 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_11912 (bit_and v_11885 (eq v_11913 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_11886 (eq v_11880 (expression.bv_nat 8 0))) (bit_and v_11885 (eq v_11907 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_11886 v_11898) (bit_and v_11885 (eq v_11900 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_11882 undef) (bit_and (notBool_ v_11882) (bit_or (bit_and v_11886 (eq (extract v_11879 8 9) (expression.bv_nat 1 1))) (bit_and v_11885 (eq v_11890 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2872 : imm int) (v_2873 : Mem) => do
      v_11969 <- evaluateAddress v_2873;
      v_11970 <- load v_11969 1;
      v_11973 <- eval (bv_and (handleImmediateWithSignExtend v_2872 8 8) (expression.bv_nat 8 31));
      v_11976 <- eval (lshr (concat v_11970 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 1 0) v_11973)));
      v_11977 <- eval (extract v_11976 0 8);
      store v_11969 v_11977 1;
      v_11979 <- eval (uge v_11973 (expression.bv_nat 8 8));
      v_11982 <- eval (eq v_11973 (expression.bv_nat 8 0));
      v_11983 <- eval (notBool_ v_11982);
      v_11987 <- getRegister cf;
      v_11995 <- eval (eq (extract v_11976 0 1) (expression.bv_nat 1 1));
      v_11997 <- getRegister sf;
      v_12004 <- getRegister zf;
      v_12009 <- eval (bit_and v_11983 undef);
      v_12010 <- getRegister af;
      v_12043 <- getRegister pf;
      v_12048 <- eval (eq v_11973 (expression.bv_nat 8 1));
      v_12053 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_12048 (eq (extract v_11970 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_12048) (bit_or v_12009 (bit_and v_11982 (eq v_12053 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_11983 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_11976 7 8) (expression.bv_nat 1 1)) (eq (extract v_11976 6 7) (expression.bv_nat 1 1)))) (eq (extract v_11976 5 6) (expression.bv_nat 1 1)))) (eq (extract v_11976 4 5) (expression.bv_nat 1 1)))) (eq (extract v_11976 3 4) (expression.bv_nat 1 1)))) (eq (extract v_11976 2 3) (expression.bv_nat 1 1)))) (eq (extract v_11976 1 2) (expression.bv_nat 1 1)))) v_11995)) (bit_and v_11982 (eq v_12043 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_12009 (bit_and v_11982 (eq v_12010 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_11983 (eq v_11977 (expression.bv_nat 8 0))) (bit_and v_11982 (eq v_12004 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_11983 v_11995) (bit_and v_11982 (eq v_11997 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_11979 undef) (bit_and (notBool_ v_11979) (bit_or (bit_and v_11983 (eq (extract v_11976 8 9) (expression.bv_nat 1 1))) (bit_and v_11982 (eq v_11987 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2876 : Mem) => do
      v_13371 <- evaluateAddress v_2876;
      v_13372 <- load v_13371 1;
      v_13374 <- eval (lshr (concat v_13372 (expression.bv_nat 1 0)) 1);
      v_13375 <- eval (extract v_13374 0 8);
      store v_13371 v_13375 1;
      setRegister of (mux (eq (extract v_13372 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_13375);
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_13375);
      setRegister sf (mux (eq (extract v_13374 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_13374 8 9) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2876 : Mem) => do
      v_13394 <- evaluateAddress v_2876;
      v_13395 <- load v_13394 1;
      v_13397 <- eval (lshr (concat v_13395 (expression.bv_nat 1 0)) 1);
      v_13398 <- eval (extract v_13397 0 8);
      store v_13394 v_13398 1;
      setRegister of (extract v_13395 0 1);
      setRegister pf (parityFlag v_13398);
      setRegister af undef;
      setRegister zf (zeroFlag v_13398);
      setRegister sf (extract v_13397 0 1);
      setRegister cf (extract v_13397 8 9);
      pure ()
    pat_end
