def addq1 : instruction :=
  definst "addq" $ do
    pattern fun (v_2709 : imm int) (v_2710 : reg (bv 64)) => do
      v_4705 <- eval (handleImmediateWithSignExtend v_2709 32 32);
      v_4706 <- eval (sext v_4705 64);
      v_4708 <- getRegister v_2710;
      v_4710 <- eval (add (concat (expression.bv_nat 1 0) v_4706) (concat (expression.bv_nat 1 0) v_4708));
      v_4711 <- eval (extract v_4710 1 65);
      setRegister (lhs.of_reg v_2710) v_4711;
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_4705 27) (isBitSet v_4708 59))) (isBitSet v_4710 60)));
      setRegister cf (isBitSet v_4710 0);
      setRegister of (overflowFlag v_4706 v_4708 v_4711);
      setRegister pf (parityFlag (extract v_4710 57 65));
      setRegister sf (isBitSet v_4710 1);
      setRegister zf (zeroFlag v_4711);
      pure ()
    pat_end;
    pattern fun (v_2718 : reg (bv 64)) (v_2719 : reg (bv 64)) => do
      v_4736 <- getRegister v_2718;
      v_4738 <- getRegister v_2719;
      v_4740 <- eval (add (concat (expression.bv_nat 1 0) v_4736) (concat (expression.bv_nat 1 0) v_4738));
      v_4741 <- eval (extract v_4740 1 65);
      setRegister (lhs.of_reg v_2719) v_4741;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4736 v_4738) 59) (isBitSet v_4740 60)));
      setRegister cf (isBitSet v_4740 0);
      setRegister of (overflowFlag v_4736 v_4738 v_4741);
      setRegister pf (parityFlag (extract v_4740 57 65));
      setRegister sf (isBitSet v_4740 1);
      setRegister zf (zeroFlag v_4741);
      pure ()
    pat_end;
    pattern fun (v_2714 : Mem) (v_2715 : reg (bv 64)) => do
      v_8800 <- evaluateAddress v_2714;
      v_8801 <- load v_8800 8;
      v_8803 <- getRegister v_2715;
      v_8805 <- eval (add (concat (expression.bv_nat 1 0) v_8801) (concat (expression.bv_nat 1 0) v_8803));
      v_8806 <- eval (extract v_8805 1 65);
      setRegister (lhs.of_reg v_2715) v_8806;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8801 v_8803) 59) (isBitSet v_8805 60)));
      setRegister cf (isBitSet v_8805 0);
      setRegister of (overflowFlag v_8801 v_8803 v_8806);
      setRegister pf (parityFlag (extract v_8805 57 65));
      setRegister sf (isBitSet v_8805 1);
      setRegister zf (zeroFlag v_8806);
      pure ()
    pat_end;
    pattern fun (v_2702 : imm int) (v_2701 : Mem) => do
      v_10181 <- evaluateAddress v_2701;
      v_10182 <- eval (handleImmediateWithSignExtend v_2702 32 32);
      v_10183 <- eval (sext v_10182 64);
      v_10185 <- load v_10181 8;
      v_10187 <- eval (add (concat (expression.bv_nat 1 0) v_10183) (concat (expression.bv_nat 1 0) v_10185));
      v_10188 <- eval (extract v_10187 1 65);
      store v_10181 v_10188 8;
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_10182 27) (isBitSet v_10185 59))) (isBitSet v_10187 60)));
      setRegister cf (isBitSet v_10187 0);
      setRegister of (overflowFlag v_10183 v_10185 v_10188);
      setRegister pf (parityFlag (extract v_10187 57 65));
      setRegister sf (isBitSet v_10187 1);
      setRegister zf (zeroFlag v_10188);
      pure ()
    pat_end;
    pattern fun (v_2706 : reg (bv 64)) (v_2705 : Mem) => do
      v_10209 <- evaluateAddress v_2705;
      v_10210 <- getRegister v_2706;
      v_10212 <- load v_10209 8;
      v_10214 <- eval (add (concat (expression.bv_nat 1 0) v_10210) (concat (expression.bv_nat 1 0) v_10212));
      v_10215 <- eval (extract v_10214 1 65);
      store v_10209 v_10215 8;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10210 v_10212) 59) (isBitSet v_10214 60)));
      setRegister cf (isBitSet v_10214 0);
      setRegister of (overflowFlag v_10210 v_10212 v_10215);
      setRegister pf (parityFlag (extract v_10214 57 65));
      setRegister sf (isBitSet v_10214 1);
      setRegister zf (zeroFlag v_10215);
      pure ()
    pat_end
