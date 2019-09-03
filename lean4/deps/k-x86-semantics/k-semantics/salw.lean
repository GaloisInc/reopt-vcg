def salw1 : instruction :=
  definst "salw" $ do
    pattern fun cl (v_2983 : reg (bv 16)) => do
      v_6817 <- getRegister rcx;
      v_6819 <- eval (bv_and (extract v_6817 56 64) (expression.bv_nat 8 31));
      v_6820 <- eval (uge v_6819 (expression.bv_nat 8 16));
      v_6823 <- eval (eq v_6819 (expression.bv_nat 8 0));
      v_6824 <- eval (notBool_ v_6823);
      v_6825 <- getRegister v_2983;
      v_6826 <- eval (concat (expression.bv_nat 1 0) v_6825);
      v_6831 <- eval (extract (shl v_6826 (uvalueMInt (concat (expression.bv_nat 9 0) v_6819))) 0 (bitwidthMInt v_6826));
      v_6835 <- getRegister cf;
      v_6840 <- eval (bit_or (bit_and v_6820 undef) (bit_and (notBool_ v_6820) (bit_or (bit_and v_6824 (eq (extract v_6831 0 1) (expression.bv_nat 1 1))) (bit_and v_6823 (eq v_6835 (expression.bv_nat 1 1))))));
      v_6843 <- eval (eq (extract v_6831 1 2) (expression.bv_nat 1 1));
      v_6845 <- getRegister sf;
      v_6850 <- eval (bit_and v_6824 undef);
      v_6851 <- getRegister af;
      v_6856 <- eval (extract v_6831 1 17);
      v_6859 <- getRegister zf;
      v_6894 <- getRegister pf;
      v_6899 <- eval (eq v_6819 (expression.bv_nat 8 1));
      v_6904 <- getRegister of;
      setRegister (lhs.of_reg v_2983) v_6856;
      setRegister of (mux (bit_or (bit_and v_6899 (notBool_ (eq v_6840 v_6843))) (bit_and (notBool_ v_6899) (bit_or v_6850 (bit_and v_6823 (eq v_6904 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_6824 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_6831 16 17) (expression.bv_nat 1 1)) (eq (extract v_6831 15 16) (expression.bv_nat 1 1)))) (eq (extract v_6831 14 15) (expression.bv_nat 1 1)))) (eq (extract v_6831 13 14) (expression.bv_nat 1 1)))) (eq (extract v_6831 12 13) (expression.bv_nat 1 1)))) (eq (extract v_6831 11 12) (expression.bv_nat 1 1)))) (eq (extract v_6831 10 11) (expression.bv_nat 1 1)))) (eq (extract v_6831 9 10) (expression.bv_nat 1 1)))) (bit_and v_6823 (eq v_6894 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_6824 (eq v_6856 (expression.bv_nat 16 0))) (bit_and v_6823 (eq v_6859 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_6850 (bit_and v_6823 (eq v_6851 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_6824 v_6843) (bit_and v_6823 (eq v_6845 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_6840 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2984 : imm int) (v_2988 : reg (bv 16)) => do
      v_6919 <- eval (bv_and (handleImmediateWithSignExtend v_2984 8 8) (expression.bv_nat 8 31));
      v_6920 <- eval (uge v_6919 (expression.bv_nat 8 16));
      v_6923 <- eval (eq v_6919 (expression.bv_nat 8 0));
      v_6924 <- eval (notBool_ v_6923);
      v_6925 <- getRegister v_2988;
      v_6926 <- eval (concat (expression.bv_nat 1 0) v_6925);
      v_6931 <- eval (extract (shl v_6926 (uvalueMInt (concat (expression.bv_nat 9 0) v_6919))) 0 (bitwidthMInt v_6926));
      v_6935 <- getRegister cf;
      v_6940 <- eval (bit_or (bit_and v_6920 undef) (bit_and (notBool_ v_6920) (bit_or (bit_and v_6924 (eq (extract v_6931 0 1) (expression.bv_nat 1 1))) (bit_and v_6923 (eq v_6935 (expression.bv_nat 1 1))))));
      v_6943 <- eval (eq (extract v_6931 1 2) (expression.bv_nat 1 1));
      v_6945 <- getRegister sf;
      v_6950 <- eval (bit_and v_6924 undef);
      v_6951 <- getRegister af;
      v_6956 <- eval (extract v_6931 1 17);
      v_6959 <- getRegister zf;
      v_6994 <- getRegister pf;
      v_6999 <- eval (eq v_6919 (expression.bv_nat 8 1));
      v_7004 <- getRegister of;
      setRegister (lhs.of_reg v_2988) v_6956;
      setRegister of (mux (bit_or (bit_and v_6999 (notBool_ (eq v_6940 v_6943))) (bit_and (notBool_ v_6999) (bit_or v_6950 (bit_and v_6923 (eq v_7004 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_6924 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_6931 16 17) (expression.bv_nat 1 1)) (eq (extract v_6931 15 16) (expression.bv_nat 1 1)))) (eq (extract v_6931 14 15) (expression.bv_nat 1 1)))) (eq (extract v_6931 13 14) (expression.bv_nat 1 1)))) (eq (extract v_6931 12 13) (expression.bv_nat 1 1)))) (eq (extract v_6931 11 12) (expression.bv_nat 1 1)))) (eq (extract v_6931 10 11) (expression.bv_nat 1 1)))) (eq (extract v_6931 9 10) (expression.bv_nat 1 1)))) (bit_and v_6923 (eq v_6994 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_6924 (eq v_6956 (expression.bv_nat 16 0))) (bit_and v_6923 (eq v_6959 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_6950 (bit_and v_6923 (eq v_6951 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_6924 v_6943) (bit_and v_6923 (eq v_6945 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_6940 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2995 : reg (bv 16)) => do
      v_7020 <- getRegister v_2995;
      v_7021 <- eval (concat (expression.bv_nat 1 0) v_7020);
      v_7024 <- eval (extract (shl v_7021 1) 0 (bitwidthMInt v_7021));
      v_7025 <- eval (extract v_7024 0 1);
      v_7026 <- eval (extract v_7024 1 2);
      v_7027 <- eval (extract v_7024 1 17);
      setRegister (lhs.of_reg v_2995) v_7027;
      setRegister of (mux (notBool_ (eq (eq v_7025 (expression.bv_nat 1 1)) (eq v_7026 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_7024 9 17));
      setRegister zf (zeroFlag v_7027);
      setRegister af undef;
      setRegister sf v_7026;
      setRegister cf v_7025;
      pure ()
    pat_end;
    pattern fun (v_2991 : reg (bv 16)) => do
      v_9669 <- getRegister v_2991;
      v_9670 <- eval (concat (expression.bv_nat 1 0) v_9669);
      v_9673 <- eval (extract (shl v_9670 1) 0 (bitwidthMInt v_9670));
      v_9675 <- eval (eq (extract v_9673 0 1) (expression.bv_nat 1 1));
      v_9678 <- eval (eq (extract v_9673 1 2) (expression.bv_nat 1 1));
      v_9680 <- eval (extract v_9673 1 17);
      setRegister (lhs.of_reg v_2991) v_9680;
      setRegister of (mux (notBool_ (eq v_9675 v_9678)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9673 9 17));
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_9680);
      setRegister sf (mux v_9678 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_9675 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2991 : reg (bv 16)) => do
      v_9694 <- getRegister v_2991;
      v_9695 <- eval (concat (expression.bv_nat 1 0) v_9694);
      v_9698 <- eval (extract (shl v_9695 1) 0 (bitwidthMInt v_9695));
      v_9699 <- eval (extract v_9698 0 1);
      v_9700 <- eval (extract v_9698 1 2);
      v_9701 <- eval (extract v_9698 1 17);
      setRegister (lhs.of_reg v_2991) v_9701;
      setRegister of (mux (notBool_ (eq (eq v_9699 (expression.bv_nat 1 1)) (eq v_9700 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9698 9 17));
      setRegister af undef;
      setRegister zf (zeroFlag v_9701);
      setRegister sf v_9700;
      setRegister cf v_9699;
      pure ()
    pat_end;
    pattern fun cl (v_2967 : Mem) => do
      v_16318 <- evaluateAddress v_2967;
      v_16319 <- load v_16318 2;
      v_16320 <- eval (concat (expression.bv_nat 1 0) v_16319);
      v_16321 <- getRegister rcx;
      v_16323 <- eval (bv_and (extract v_16321 56 64) (expression.bv_nat 8 31));
      v_16328 <- eval (extract (shl v_16320 (uvalueMInt (concat (expression.bv_nat 9 0) v_16323))) 0 (bitwidthMInt v_16320));
      v_16329 <- eval (extract v_16328 1 17);
      store v_16318 v_16329 2;
      v_16331 <- eval (uge v_16323 (expression.bv_nat 8 16));
      v_16334 <- eval (eq v_16323 (expression.bv_nat 8 0));
      v_16335 <- eval (notBool_ v_16334);
      v_16339 <- getRegister cf;
      v_16344 <- eval (bit_or (bit_and v_16331 undef) (bit_and (notBool_ v_16331) (bit_or (bit_and v_16335 (eq (extract v_16328 0 1) (expression.bv_nat 1 1))) (bit_and v_16334 (eq v_16339 (expression.bv_nat 1 1))))));
      v_16347 <- eval (eq (extract v_16328 1 2) (expression.bv_nat 1 1));
      v_16349 <- getRegister sf;
      v_16356 <- getRegister zf;
      v_16361 <- eval (bit_and v_16335 undef);
      v_16362 <- getRegister af;
      v_16397 <- getRegister pf;
      v_16402 <- eval (eq v_16323 (expression.bv_nat 8 1));
      v_16407 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_16402 (notBool_ (eq v_16344 v_16347))) (bit_and (notBool_ v_16402) (bit_or v_16361 (bit_and v_16334 (eq v_16407 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_16335 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_16328 16 17) (expression.bv_nat 1 1)) (eq (extract v_16328 15 16) (expression.bv_nat 1 1)))) (eq (extract v_16328 14 15) (expression.bv_nat 1 1)))) (eq (extract v_16328 13 14) (expression.bv_nat 1 1)))) (eq (extract v_16328 12 13) (expression.bv_nat 1 1)))) (eq (extract v_16328 11 12) (expression.bv_nat 1 1)))) (eq (extract v_16328 10 11) (expression.bv_nat 1 1)))) (eq (extract v_16328 9 10) (expression.bv_nat 1 1)))) (bit_and v_16334 (eq v_16397 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_16361 (bit_and v_16334 (eq v_16362 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_16335 (eq v_16329 (expression.bv_nat 16 0))) (bit_and v_16334 (eq v_16356 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_16335 v_16347) (bit_and v_16334 (eq v_16349 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_16344 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2970 : imm int) (v_2971 : Mem) => do
      v_16420 <- evaluateAddress v_2971;
      v_16421 <- load v_16420 2;
      v_16422 <- eval (concat (expression.bv_nat 1 0) v_16421);
      v_16424 <- eval (bv_and (handleImmediateWithSignExtend v_2970 8 8) (expression.bv_nat 8 31));
      v_16429 <- eval (extract (shl v_16422 (uvalueMInt (concat (expression.bv_nat 9 0) v_16424))) 0 (bitwidthMInt v_16422));
      v_16430 <- eval (extract v_16429 1 17);
      store v_16420 v_16430 2;
      v_16432 <- eval (uge v_16424 (expression.bv_nat 8 16));
      v_16435 <- eval (eq v_16424 (expression.bv_nat 8 0));
      v_16436 <- eval (notBool_ v_16435);
      v_16440 <- getRegister cf;
      v_16445 <- eval (bit_or (bit_and v_16432 undef) (bit_and (notBool_ v_16432) (bit_or (bit_and v_16436 (eq (extract v_16429 0 1) (expression.bv_nat 1 1))) (bit_and v_16435 (eq v_16440 (expression.bv_nat 1 1))))));
      v_16448 <- eval (eq (extract v_16429 1 2) (expression.bv_nat 1 1));
      v_16450 <- getRegister sf;
      v_16457 <- getRegister zf;
      v_16462 <- eval (bit_and v_16436 undef);
      v_16463 <- getRegister af;
      v_16498 <- getRegister pf;
      v_16503 <- eval (eq v_16424 (expression.bv_nat 8 1));
      v_16508 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_16503 (notBool_ (eq v_16445 v_16448))) (bit_and (notBool_ v_16503) (bit_or v_16462 (bit_and v_16435 (eq v_16508 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_16436 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_16429 16 17) (expression.bv_nat 1 1)) (eq (extract v_16429 15 16) (expression.bv_nat 1 1)))) (eq (extract v_16429 14 15) (expression.bv_nat 1 1)))) (eq (extract v_16429 13 14) (expression.bv_nat 1 1)))) (eq (extract v_16429 12 13) (expression.bv_nat 1 1)))) (eq (extract v_16429 11 12) (expression.bv_nat 1 1)))) (eq (extract v_16429 10 11) (expression.bv_nat 1 1)))) (eq (extract v_16429 9 10) (expression.bv_nat 1 1)))) (bit_and v_16435 (eq v_16498 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_16462 (bit_and v_16435 (eq v_16463 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_16436 (eq v_16430 (expression.bv_nat 16 0))) (bit_and v_16435 (eq v_16457 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_16436 v_16448) (bit_and v_16435 (eq v_16450 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_16445 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2976 : Mem) => do
      v_18346 <- evaluateAddress v_2976;
      v_18347 <- load v_18346 2;
      v_18348 <- eval (concat (expression.bv_nat 1 0) v_18347);
      v_18351 <- eval (extract (shl v_18348 1) 0 (bitwidthMInt v_18348));
      v_18352 <- eval (extract v_18351 1 17);
      store v_18346 v_18352 2;
      v_18355 <- eval (eq (extract v_18351 0 1) (expression.bv_nat 1 1));
      v_18358 <- eval (eq (extract v_18351 1 2) (expression.bv_nat 1 1));
      setRegister of (mux (notBool_ (eq v_18355 v_18358)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_18351 9 17));
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_18352);
      setRegister sf (mux v_18358 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_18355 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2976 : Mem) => do
      v_18372 <- evaluateAddress v_2976;
      v_18373 <- load v_18372 2;
      v_18374 <- eval (concat (expression.bv_nat 1 0) v_18373);
      v_18377 <- eval (extract (shl v_18374 1) 0 (bitwidthMInt v_18374));
      v_18378 <- eval (extract v_18377 1 17);
      store v_18372 v_18378 2;
      v_18380 <- eval (extract v_18377 0 1);
      v_18381 <- eval (extract v_18377 1 2);
      setRegister of (mux (notBool_ (eq (eq v_18380 (expression.bv_nat 1 1)) (eq v_18381 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_18377 9 17));
      setRegister af undef;
      setRegister zf (zeroFlag v_18378);
      setRegister sf v_18381;
      setRegister cf v_18380;
      pure ()
    pat_end
