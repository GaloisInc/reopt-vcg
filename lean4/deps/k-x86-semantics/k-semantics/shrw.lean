def shrw1 : instruction :=
  definst "shrw" $ do
    pattern fun cl (v_2986 : reg (bv 16)) => do
      v_6400 <- getRegister rcx;
      v_6402 <- eval (bv_and (extract v_6400 56 64) (expression.bv_nat 8 31));
      v_6403 <- eval (uge v_6402 (expression.bv_nat 8 16));
      v_6406 <- eval (eq v_6402 (expression.bv_nat 8 0));
      v_6407 <- eval (notBool_ v_6406);
      v_6408 <- getRegister v_2986;
      v_6412 <- eval (lshr (concat v_6408 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 9 0) v_6402)));
      v_6416 <- getRegister cf;
      v_6426 <- getRegister sf;
      v_6431 <- eval (bit_and v_6407 undef);
      v_6432 <- getRegister af;
      v_6437 <- eval (extract v_6412 0 16);
      v_6440 <- getRegister zf;
      v_6475 <- getRegister pf;
      v_6480 <- eval (eq v_6402 (expression.bv_nat 8 1));
      v_6485 <- getRegister of;
      setRegister (lhs.of_reg v_2986) v_6437;
      setRegister of (mux (bit_or (bit_and v_6480 (eq (extract v_6408 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_6480) (bit_or v_6431 (bit_and v_6406 (eq v_6485 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_6407 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_6412 15 16) (expression.bv_nat 1 1)) (eq (extract v_6412 14 15) (expression.bv_nat 1 1)))) (eq (extract v_6412 13 14) (expression.bv_nat 1 1)))) (eq (extract v_6412 12 13) (expression.bv_nat 1 1)))) (eq (extract v_6412 11 12) (expression.bv_nat 1 1)))) (eq (extract v_6412 10 11) (expression.bv_nat 1 1)))) (eq (extract v_6412 9 10) (expression.bv_nat 1 1)))) (eq (extract v_6412 8 9) (expression.bv_nat 1 1)))) (bit_and v_6406 (eq v_6475 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_6407 (eq v_6437 (expression.bv_nat 16 0))) (bit_and v_6406 (eq v_6440 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_6431 (bit_and v_6406 (eq v_6432 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_6407 (eq (extract v_6412 0 1) (expression.bv_nat 1 1))) (bit_and v_6406 (eq v_6426 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_6403 undef) (bit_and (notBool_ v_6403) (bit_or (bit_and v_6407 (eq (extract v_6412 16 17) (expression.bv_nat 1 1))) (bit_and v_6406 (eq v_6416 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2989 : imm int) (v_2991 : reg (bv 16)) => do
      v_6500 <- eval (bv_and (handleImmediateWithSignExtend v_2989 8 8) (expression.bv_nat 8 31));
      v_6501 <- eval (uge v_6500 (expression.bv_nat 8 16));
      v_6504 <- eval (eq v_6500 (expression.bv_nat 8 0));
      v_6505 <- eval (notBool_ v_6504);
      v_6506 <- getRegister v_2991;
      v_6510 <- eval (lshr (concat v_6506 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 9 0) v_6500)));
      v_6514 <- getRegister cf;
      v_6524 <- getRegister sf;
      v_6529 <- eval (bit_and v_6505 undef);
      v_6530 <- getRegister af;
      v_6535 <- eval (extract v_6510 0 16);
      v_6538 <- getRegister zf;
      v_6573 <- getRegister pf;
      v_6578 <- eval (eq v_6500 (expression.bv_nat 8 1));
      v_6583 <- getRegister of;
      setRegister (lhs.of_reg v_2991) v_6535;
      setRegister of (mux (bit_or (bit_and v_6578 (eq (extract v_6506 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_6578) (bit_or v_6529 (bit_and v_6504 (eq v_6583 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_6505 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_6510 15 16) (expression.bv_nat 1 1)) (eq (extract v_6510 14 15) (expression.bv_nat 1 1)))) (eq (extract v_6510 13 14) (expression.bv_nat 1 1)))) (eq (extract v_6510 12 13) (expression.bv_nat 1 1)))) (eq (extract v_6510 11 12) (expression.bv_nat 1 1)))) (eq (extract v_6510 10 11) (expression.bv_nat 1 1)))) (eq (extract v_6510 9 10) (expression.bv_nat 1 1)))) (eq (extract v_6510 8 9) (expression.bv_nat 1 1)))) (bit_and v_6504 (eq v_6573 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_6505 (eq v_6535 (expression.bv_nat 16 0))) (bit_and v_6504 (eq v_6538 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_6529 (bit_and v_6504 (eq v_6530 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_6505 (eq (extract v_6510 0 1) (expression.bv_nat 1 1))) (bit_and v_6504 (eq v_6524 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_6501 undef) (bit_and (notBool_ v_6501) (bit_or (bit_and v_6505 (eq (extract v_6510 16 17) (expression.bv_nat 1 1))) (bit_and v_6504 (eq v_6514 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2998 : reg (bv 16)) => do
      v_6599 <- getRegister v_2998;
      v_6601 <- eval (lshr (concat v_6599 (expression.bv_nat 1 0)) 1);
      v_6604 <- eval (extract v_6601 0 16);
      setRegister (lhs.of_reg v_2998) v_6604;
      setRegister of (extract v_6599 0 1);
      setRegister pf (parityFlag (extract v_6601 8 16));
      setRegister zf (zeroFlag v_6604);
      setRegister af undef;
      setRegister sf (extract v_6601 0 1);
      setRegister cf (extract v_6601 16 17);
      pure ()
    pat_end;
    pattern fun (v_2994 : reg (bv 16)) => do
      v_8139 <- getRegister v_2994;
      v_8141 <- eval (lshr (concat v_8139 (expression.bv_nat 1 0)) 1);
      v_8148 <- eval (extract v_8141 0 16);
      setRegister (lhs.of_reg v_2994) v_8148;
      setRegister of (mux (eq (extract v_8139 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8141 8 16));
      setRegister zf (zeroFlag v_8148);
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (eq (extract v_8141 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_8141 16 17) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2994 : reg (bv 16)) => do
      v_8162 <- getRegister v_2994;
      v_8164 <- eval (lshr (concat v_8162 (expression.bv_nat 1 0)) 1);
      v_8167 <- eval (extract v_8164 0 16);
      setRegister (lhs.of_reg v_2994) v_8167;
      setRegister of (extract v_8162 0 1);
      setRegister pf (parityFlag (extract v_8164 8 16));
      setRegister zf (zeroFlag v_8167);
      setRegister af undef;
      setRegister sf (extract v_8164 0 1);
      setRegister cf (extract v_8164 16 17);
      pure ()
    pat_end;
    pattern fun cl (v_2972 : Mem) => do
      v_12718 <- evaluateAddress v_2972;
      v_12719 <- load v_12718 2;
      v_12721 <- getRegister rcx;
      v_12723 <- eval (bv_and (extract v_12721 56 64) (expression.bv_nat 8 31));
      v_12726 <- eval (lshr (concat v_12719 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 9 0) v_12723)));
      v_12727 <- eval (extract v_12726 0 16);
      store v_12718 v_12727 2;
      v_12729 <- eval (uge v_12723 (expression.bv_nat 8 16));
      v_12732 <- eval (eq v_12723 (expression.bv_nat 8 0));
      v_12733 <- eval (notBool_ v_12732);
      v_12737 <- getRegister cf;
      v_12747 <- getRegister sf;
      v_12754 <- getRegister zf;
      v_12759 <- eval (bit_and v_12733 undef);
      v_12760 <- getRegister af;
      v_12795 <- getRegister pf;
      v_12800 <- eval (eq v_12723 (expression.bv_nat 8 1));
      v_12805 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_12800 (eq (extract v_12719 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_12800) (bit_or v_12759 (bit_and v_12732 (eq v_12805 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_12733 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_12726 15 16) (expression.bv_nat 1 1)) (eq (extract v_12726 14 15) (expression.bv_nat 1 1)))) (eq (extract v_12726 13 14) (expression.bv_nat 1 1)))) (eq (extract v_12726 12 13) (expression.bv_nat 1 1)))) (eq (extract v_12726 11 12) (expression.bv_nat 1 1)))) (eq (extract v_12726 10 11) (expression.bv_nat 1 1)))) (eq (extract v_12726 9 10) (expression.bv_nat 1 1)))) (eq (extract v_12726 8 9) (expression.bv_nat 1 1)))) (bit_and v_12732 (eq v_12795 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_12759 (bit_and v_12732 (eq v_12760 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_12733 (eq v_12727 (expression.bv_nat 16 0))) (bit_and v_12732 (eq v_12754 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_12733 (eq (extract v_12726 0 1) (expression.bv_nat 1 1))) (bit_and v_12732 (eq v_12747 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_12729 undef) (bit_and (notBool_ v_12729) (bit_or (bit_and v_12733 (eq (extract v_12726 16 17) (expression.bv_nat 1 1))) (bit_and v_12732 (eq v_12737 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2975 : imm int) (v_2976 : Mem) => do
      v_12818 <- evaluateAddress v_2976;
      v_12819 <- load v_12818 2;
      v_12822 <- eval (bv_and (handleImmediateWithSignExtend v_2975 8 8) (expression.bv_nat 8 31));
      v_12825 <- eval (lshr (concat v_12819 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 9 0) v_12822)));
      v_12826 <- eval (extract v_12825 0 16);
      store v_12818 v_12826 2;
      v_12828 <- eval (uge v_12822 (expression.bv_nat 8 16));
      v_12831 <- eval (eq v_12822 (expression.bv_nat 8 0));
      v_12832 <- eval (notBool_ v_12831);
      v_12836 <- getRegister cf;
      v_12846 <- getRegister sf;
      v_12853 <- getRegister zf;
      v_12858 <- eval (bit_and v_12832 undef);
      v_12859 <- getRegister af;
      v_12894 <- getRegister pf;
      v_12899 <- eval (eq v_12822 (expression.bv_nat 8 1));
      v_12904 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_12899 (eq (extract v_12819 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_12899) (bit_or v_12858 (bit_and v_12831 (eq v_12904 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_12832 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_12825 15 16) (expression.bv_nat 1 1)) (eq (extract v_12825 14 15) (expression.bv_nat 1 1)))) (eq (extract v_12825 13 14) (expression.bv_nat 1 1)))) (eq (extract v_12825 12 13) (expression.bv_nat 1 1)))) (eq (extract v_12825 11 12) (expression.bv_nat 1 1)))) (eq (extract v_12825 10 11) (expression.bv_nat 1 1)))) (eq (extract v_12825 9 10) (expression.bv_nat 1 1)))) (eq (extract v_12825 8 9) (expression.bv_nat 1 1)))) (bit_and v_12831 (eq v_12894 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_12858 (bit_and v_12831 (eq v_12859 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_12832 (eq v_12826 (expression.bv_nat 16 0))) (bit_and v_12831 (eq v_12853 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_12832 (eq (extract v_12825 0 1) (expression.bv_nat 1 1))) (bit_and v_12831 (eq v_12846 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_12828 undef) (bit_and (notBool_ v_12828) (bit_or (bit_and v_12832 (eq (extract v_12825 16 17) (expression.bv_nat 1 1))) (bit_and v_12831 (eq v_12836 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2979 : Mem) => do
      v_13495 <- evaluateAddress v_2979;
      v_13496 <- load v_13495 2;
      v_13498 <- eval (lshr (concat v_13496 (expression.bv_nat 1 0)) 1);
      v_13499 <- eval (extract v_13498 0 16);
      store v_13495 v_13499 2;
      setRegister of (mux (eq (extract v_13496 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_13498 8 16));
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_13499);
      setRegister sf (mux (eq (extract v_13498 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_13498 16 17) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2979 : Mem) => do
      v_13519 <- evaluateAddress v_2979;
      v_13520 <- load v_13519 2;
      v_13522 <- eval (lshr (concat v_13520 (expression.bv_nat 1 0)) 1);
      v_13523 <- eval (extract v_13522 0 16);
      store v_13519 v_13523 2;
      setRegister of (extract v_13520 0 1);
      setRegister pf (parityFlag (extract v_13522 8 16));
      setRegister af undef;
      setRegister zf (zeroFlag v_13523);
      setRegister sf (extract v_13522 0 1);
      setRegister cf (extract v_13522 16 17);
      pure ()
    pat_end
