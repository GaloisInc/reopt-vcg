def sbbq1 : instruction :=
  definst "sbbq" $ do
    pattern fun (v_3352 : imm int) (v_3349 : reg (bv 64)) => do
      v_6789 <- getRegister cf;
      v_6790 <- eval (handleImmediateWithSignExtend v_3352 32 32);
      v_6791 <- eval (sext v_6790 64);
      v_6793 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_6791 (expression.bv_nat 64 18446744073709551615)));
      v_6796 <- getRegister v_3349;
      v_6798 <- eval (add (mux v_6789 v_6793 (add v_6793 (expression.bv_nat 65 1))) (concat (expression.bv_nat 1 0) v_6796));
      v_6799 <- eval (extract v_6798 1 65);
      v_6801 <- eval (isBitSet v_6798 1);
      v_6806 <- eval (eq (bv_xor (extract v_6791 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3349) v_6799;
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_6790 27) (isBitSet v_6796 59))) (isBitSet v_6798 60)));
      setRegister cf (isBitClear v_6798 0);
      setRegister of (bit_and (eq v_6806 (isBitSet v_6796 0)) (notBool_ (eq v_6806 v_6801)));
      setRegister pf (parityFlag (extract v_6798 57 65));
      setRegister sf v_6801;
      setRegister zf (zeroFlag v_6799);
      pure ()
    pat_end;
    pattern fun (v_3358 : reg (bv 64)) (v_3359 : reg (bv 64)) => do
      v_6831 <- getRegister cf;
      v_6832 <- getRegister v_3358;
      v_6834 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_6832 (expression.bv_nat 64 18446744073709551615)));
      v_6837 <- getRegister v_3359;
      v_6839 <- eval (add (mux v_6831 v_6834 (add v_6834 (expression.bv_nat 65 1))) (concat (expression.bv_nat 1 0) v_6837));
      v_6840 <- eval (extract v_6839 1 65);
      v_6842 <- eval (isBitSet v_6839 1);
      v_6847 <- eval (eq (bv_xor (extract v_6832 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3359) v_6840;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_6832 v_6837) 59) (isBitSet v_6839 60)));
      setRegister cf (isBitClear v_6839 0);
      setRegister of (bit_and (eq v_6847 (isBitSet v_6837 0)) (notBool_ (eq v_6847 v_6842)));
      setRegister pf (parityFlag (extract v_6839 57 65));
      setRegister sf v_6842;
      setRegister zf (zeroFlag v_6840);
      pure ()
    pat_end;
    pattern fun (v_3355 : Mem) (v_3354 : reg (bv 64)) => do
      v_10798 <- getRegister cf;
      v_10799 <- evaluateAddress v_3355;
      v_10800 <- load v_10799 8;
      v_10802 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_10800 (expression.bv_nat 64 18446744073709551615)));
      v_10805 <- getRegister v_3354;
      v_10807 <- eval (add (mux v_10798 v_10802 (add v_10802 (expression.bv_nat 65 1))) (concat (expression.bv_nat 1 0) v_10805));
      v_10808 <- eval (extract v_10807 1 65);
      v_10810 <- eval (isBitSet v_10807 1);
      v_10815 <- eval (eq (bv_xor (extract v_10800 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3354) v_10808;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10800 v_10805) 59) (isBitSet v_10807 60)));
      setRegister cf (isBitClear v_10807 0);
      setRegister of (bit_and (eq v_10815 (isBitSet v_10805 0)) (notBool_ (eq v_10815 v_10810)));
      setRegister pf (parityFlag (extract v_10807 57 65));
      setRegister sf v_10810;
      setRegister zf (zeroFlag v_10808);
      pure ()
    pat_end;
    pattern fun (v_3344 : imm int) (v_3341 : Mem) => do
      v_12958 <- evaluateAddress v_3341;
      v_12959 <- getRegister cf;
      v_12960 <- eval (handleImmediateWithSignExtend v_3344 32 32);
      v_12961 <- eval (sext v_12960 64);
      v_12963 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_12961 (expression.bv_nat 64 18446744073709551615)));
      v_12966 <- load v_12958 8;
      v_12968 <- eval (add (mux v_12959 v_12963 (add v_12963 (expression.bv_nat 65 1))) (concat (expression.bv_nat 1 0) v_12966));
      v_12969 <- eval (extract v_12968 1 65);
      store v_12958 v_12969 8;
      v_12972 <- eval (isBitSet v_12968 1);
      v_12977 <- eval (eq (bv_xor (extract v_12961 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_12960 27) (isBitSet v_12966 59))) (isBitSet v_12968 60)));
      setRegister cf (isBitClear v_12968 0);
      setRegister of (bit_and (eq v_12977 (isBitSet v_12966 0)) (notBool_ (eq v_12977 v_12972)));
      setRegister pf (parityFlag (extract v_12968 57 65));
      setRegister sf v_12972;
      setRegister zf (zeroFlag v_12969);
      pure ()
    pat_end;
    pattern fun (v_3345 : reg (bv 64)) (v_3346 : Mem) => do
      v_12997 <- evaluateAddress v_3346;
      v_12998 <- getRegister cf;
      v_12999 <- getRegister v_3345;
      v_13001 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_12999 (expression.bv_nat 64 18446744073709551615)));
      v_13004 <- load v_12997 8;
      v_13006 <- eval (add (mux v_12998 v_13001 (add v_13001 (expression.bv_nat 65 1))) (concat (expression.bv_nat 1 0) v_13004));
      v_13007 <- eval (extract v_13006 1 65);
      store v_12997 v_13007 8;
      v_13010 <- eval (isBitSet v_13006 1);
      v_13015 <- eval (eq (bv_xor (extract v_12999 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_12999 v_13004) 59) (isBitSet v_13006 60)));
      setRegister cf (isBitClear v_13006 0);
      setRegister of (bit_and (eq v_13015 (isBitSet v_13004 0)) (notBool_ (eq v_13015 v_13010)));
      setRegister pf (parityFlag (extract v_13006 57 65));
      setRegister sf v_13010;
      setRegister zf (zeroFlag v_13007);
      pure ()
    pat_end
