def addw1 : instruction :=
  definst "addw" $ do
    pattern fun (v_2749 : imm int) (v_2746 : reg (bv 16)) => do
      v_5022 <- eval (handleImmediateWithSignExtend v_2749 16 16);
      v_5024 <- getRegister v_2746;
      v_5026 <- eval (add (concat (expression.bv_nat 1 0) v_5022) (concat (expression.bv_nat 1 0) v_5024));
      v_5027 <- eval (extract v_5026 1 17);
      v_5029 <- eval (isBitSet v_5026 1);
      v_5032 <- eval (isBitSet v_5022 0);
      setRegister (lhs.of_reg v_2746) v_5027;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_5022 v_5024) 11) (isBitSet v_5026 12)));
      setRegister cf (isBitSet v_5026 0);
      setRegister of (bit_and (eq v_5032 (isBitSet v_5024 0)) (notBool_ (eq v_5032 v_5029)));
      setRegister pf (parityFlag (extract v_5026 9 17));
      setRegister sf v_5029;
      setRegister zf (zeroFlag v_5027);
      pure ()
    pat_end;
    pattern fun (v_2755 : reg (bv 16)) (v_2756 : reg (bv 16)) => do
      v_5055 <- getRegister v_2755;
      v_5057 <- getRegister v_2756;
      v_5059 <- eval (add (concat (expression.bv_nat 1 0) v_5055) (concat (expression.bv_nat 1 0) v_5057));
      v_5060 <- eval (extract v_5059 1 17);
      v_5062 <- eval (isBitSet v_5059 1);
      v_5065 <- eval (isBitSet v_5055 0);
      setRegister (lhs.of_reg v_2756) v_5060;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_5055 v_5057) 11) (isBitSet v_5059 12)));
      setRegister cf (isBitSet v_5059 0);
      setRegister of (bit_and (eq v_5065 (isBitSet v_5057 0)) (notBool_ (eq v_5065 v_5062)));
      setRegister pf (parityFlag (extract v_5059 9 17));
      setRegister sf v_5062;
      setRegister zf (zeroFlag v_5060);
      pure ()
    pat_end;
    pattern fun (v_2754 : Mem) (v_2751 : reg (bv 16)) => do
      v_9068 <- evaluateAddress v_2754;
      v_9069 <- load v_9068 2;
      v_9071 <- getRegister v_2751;
      v_9073 <- eval (add (concat (expression.bv_nat 1 0) v_9069) (concat (expression.bv_nat 1 0) v_9071));
      v_9074 <- eval (extract v_9073 1 17);
      v_9076 <- eval (isBitSet v_9073 1);
      v_9079 <- eval (isBitSet v_9069 0);
      setRegister (lhs.of_reg v_2751) v_9074;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_9069 v_9071) 11) (isBitSet v_9073 12)));
      setRegister cf (isBitSet v_9073 0);
      setRegister of (bit_and (eq v_9079 (isBitSet v_9071 0)) (notBool_ (eq v_9079 v_9076)));
      setRegister pf (parityFlag (extract v_9073 9 17));
      setRegister sf v_9076;
      setRegister zf (zeroFlag v_9074);
      pure ()
    pat_end;
    pattern fun (v_2740 : imm int) (v_2741 : Mem) => do
      v_10500 <- evaluateAddress v_2741;
      v_10501 <- eval (handleImmediateWithSignExtend v_2740 16 16);
      v_10503 <- load v_10500 2;
      v_10505 <- eval (add (concat (expression.bv_nat 1 0) v_10501) (concat (expression.bv_nat 1 0) v_10503));
      v_10506 <- eval (extract v_10505 1 17);
      store v_10500 v_10506 2;
      v_10509 <- eval (isBitSet v_10505 1);
      v_10512 <- eval (isBitSet v_10501 0);
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10501 v_10503) 11) (isBitSet v_10505 12)));
      setRegister cf (isBitSet v_10505 0);
      setRegister of (bit_and (eq v_10512 (isBitSet v_10503 0)) (notBool_ (eq v_10512 v_10509)));
      setRegister pf (parityFlag (extract v_10505 9 17));
      setRegister sf v_10509;
      setRegister zf (zeroFlag v_10506);
      pure ()
    pat_end;
    pattern fun (v_2742 : reg (bv 16)) (v_2745 : Mem) => do
      v_10530 <- evaluateAddress v_2745;
      v_10531 <- getRegister v_2742;
      v_10533 <- load v_10530 2;
      v_10535 <- eval (add (concat (expression.bv_nat 1 0) v_10531) (concat (expression.bv_nat 1 0) v_10533));
      v_10536 <- eval (extract v_10535 1 17);
      store v_10530 v_10536 2;
      v_10539 <- eval (isBitSet v_10535 1);
      v_10542 <- eval (isBitSet v_10531 0);
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10531 v_10533) 11) (isBitSet v_10535 12)));
      setRegister cf (isBitSet v_10535 0);
      setRegister of (bit_and (eq v_10542 (isBitSet v_10533 0)) (notBool_ (eq v_10542 v_10539)));
      setRegister pf (parityFlag (extract v_10535 9 17));
      setRegister sf v_10539;
      setRegister zf (zeroFlag v_10536);
      pure ()
    pat_end
