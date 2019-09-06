def sbbl1 : instruction :=
  definst "sbbl" $ do
    pattern fun (v_3329 : imm int) (v_3330 : reg (bv 32)) => do
      v_6707 <- getRegister cf;
      v_6708 <- eval (handleImmediateWithSignExtend v_3329 32 32);
      v_6710 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_6708 (expression.bv_nat 32 4294967295)));
      v_6713 <- getRegister v_3330;
      v_6715 <- eval (add (mux v_6707 v_6710 (add v_6710 (expression.bv_nat 33 1))) (concat (expression.bv_nat 1 0) v_6713));
      v_6716 <- eval (extract v_6715 1 33);
      v_6718 <- eval (isBitSet v_6715 1);
      v_6723 <- eval (eq (bv_xor (extract v_6708 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3330) v_6716;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_6708 v_6713) 27) (isBitSet v_6715 28)));
      setRegister cf (isBitClear v_6715 0);
      setRegister of (bit_and (eq v_6723 (isBitSet v_6713 0)) (notBool_ (eq v_6723 v_6718)));
      setRegister pf (parityFlag (extract v_6715 25 33));
      setRegister sf v_6718;
      setRegister zf (zeroFlag v_6716);
      pure ()
    pat_end;
    pattern fun (v_3338 : reg (bv 32)) (v_3339 : reg (bv 32)) => do
      v_6746 <- getRegister cf;
      v_6747 <- getRegister v_3338;
      v_6749 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_6747 (expression.bv_nat 32 4294967295)));
      v_6752 <- getRegister v_3339;
      v_6754 <- eval (add (mux v_6746 v_6749 (add v_6749 (expression.bv_nat 33 1))) (concat (expression.bv_nat 1 0) v_6752));
      v_6755 <- eval (extract v_6754 1 33);
      v_6757 <- eval (isBitSet v_6754 1);
      v_6762 <- eval (eq (bv_xor (extract v_6747 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3339) v_6755;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_6747 v_6752) 27) (isBitSet v_6754 28)));
      setRegister cf (isBitClear v_6754 0);
      setRegister of (bit_and (eq v_6762 (isBitSet v_6752 0)) (notBool_ (eq v_6762 v_6757)));
      setRegister pf (parityFlag (extract v_6754 25 33));
      setRegister sf v_6757;
      setRegister zf (zeroFlag v_6755);
      pure ()
    pat_end;
    pattern fun (v_3332 : Mem) (v_3335 : reg (bv 32)) => do
      v_10760 <- getRegister cf;
      v_10761 <- evaluateAddress v_3332;
      v_10762 <- load v_10761 4;
      v_10764 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_10762 (expression.bv_nat 32 4294967295)));
      v_10767 <- getRegister v_3335;
      v_10769 <- eval (add (mux v_10760 v_10764 (add v_10764 (expression.bv_nat 33 1))) (concat (expression.bv_nat 1 0) v_10767));
      v_10770 <- eval (extract v_10769 1 33);
      v_10772 <- eval (isBitSet v_10769 1);
      v_10777 <- eval (eq (bv_xor (extract v_10762 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3335) v_10770;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10762 v_10767) 27) (isBitSet v_10769 28)));
      setRegister cf (isBitClear v_10769 0);
      setRegister of (bit_and (eq v_10777 (isBitSet v_10767 0)) (notBool_ (eq v_10777 v_10772)));
      setRegister pf (parityFlag (extract v_10769 25 33));
      setRegister sf v_10772;
      setRegister zf (zeroFlag v_10770);
      pure ()
    pat_end;
    pattern fun (v_3322 : imm int) (v_3319 : Mem) => do
      v_12886 <- evaluateAddress v_3319;
      v_12887 <- getRegister cf;
      v_12888 <- eval (handleImmediateWithSignExtend v_3322 32 32);
      v_12890 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_12888 (expression.bv_nat 32 4294967295)));
      v_12893 <- load v_12886 4;
      v_12895 <- eval (add (mux v_12887 v_12890 (add v_12890 (expression.bv_nat 33 1))) (concat (expression.bv_nat 1 0) v_12893));
      v_12896 <- eval (extract v_12895 1 33);
      store v_12886 v_12896 4;
      v_12899 <- eval (isBitSet v_12895 1);
      v_12904 <- eval (eq (bv_xor (extract v_12888 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_12888 v_12893) 27) (isBitSet v_12895 28)));
      setRegister cf (isBitClear v_12895 0);
      setRegister of (bit_and (eq v_12904 (isBitSet v_12893 0)) (notBool_ (eq v_12904 v_12899)));
      setRegister pf (parityFlag (extract v_12895 25 33));
      setRegister sf v_12899;
      setRegister zf (zeroFlag v_12896);
      pure ()
    pat_end;
    pattern fun (v_3326 : reg (bv 32)) (v_3323 : Mem) => do
      v_12922 <- evaluateAddress v_3323;
      v_12923 <- getRegister cf;
      v_12924 <- getRegister v_3326;
      v_12926 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_12924 (expression.bv_nat 32 4294967295)));
      v_12929 <- load v_12922 4;
      v_12931 <- eval (add (mux v_12923 v_12926 (add v_12926 (expression.bv_nat 33 1))) (concat (expression.bv_nat 1 0) v_12929));
      v_12932 <- eval (extract v_12931 1 33);
      store v_12922 v_12932 4;
      v_12935 <- eval (isBitSet v_12931 1);
      v_12940 <- eval (eq (bv_xor (extract v_12924 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_12924 v_12929) 27) (isBitSet v_12931 28)));
      setRegister cf (isBitClear v_12931 0);
      setRegister of (bit_and (eq v_12940 (isBitSet v_12929 0)) (notBool_ (eq v_12940 v_12935)));
      setRegister pf (parityFlag (extract v_12931 25 33));
      setRegister sf v_12935;
      setRegister zf (zeroFlag v_12932);
      pure ()
    pat_end
