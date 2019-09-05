def cmpw1 : instruction :=
  definst "cmpw" $ do
    pattern fun (v_2484 : imm int) (v_2483 : reg (bv 16)) => do
      v_3957 <- eval (handleImmediateWithSignExtend v_2484 16 16);
      v_3961 <- getRegister v_2483;
      v_3963 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_3957 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_3961));
      v_3966 <- eval (isBitSet v_3963 1);
      v_3971 <- eval (eq (bv_xor (extract v_3957 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3957 v_3961) 11) (isBitSet v_3963 12)));
      setRegister cf (notBool_ (isBitSet v_3963 0));
      setRegister of (bit_and (eq v_3971 (isBitSet v_3961 0)) (notBool_ (eq v_3971 v_3966)));
      setRegister pf (parityFlag (extract v_3963 9 17));
      setRegister sf v_3966;
      setRegister zf (zeroFlag (extract v_3963 1 17));
      pure ()
    pat_end;
    pattern fun (v_2492 : reg (bv 16)) (v_2493 : reg (bv 16)) => do
      v_3994 <- getRegister v_2492;
      v_3998 <- getRegister v_2493;
      v_4000 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_3994 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_3998));
      v_4003 <- eval (isBitSet v_4000 1);
      v_4008 <- eval (eq (bv_xor (extract v_3994 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3994 v_3998) 11) (isBitSet v_4000 12)));
      setRegister cf (notBool_ (isBitSet v_4000 0));
      setRegister of (bit_and (eq v_4008 (isBitSet v_3998 0)) (notBool_ (eq v_4008 v_4003)));
      setRegister pf (parityFlag (extract v_4000 9 17));
      setRegister sf v_4003;
      setRegister zf (zeroFlag (extract v_4000 1 17));
      pure ()
    pat_end;
    pattern fun (v_2475 : imm int) (v_2474 : Mem) => do
      v_7661 <- eval (handleImmediateWithSignExtend v_2475 16 16);
      v_7665 <- evaluateAddress v_2474;
      v_7666 <- load v_7665 2;
      v_7668 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7661 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_7666));
      v_7671 <- eval (isBitSet v_7668 1);
      v_7676 <- eval (eq (bv_xor (extract v_7661 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_7661 v_7666) 11) (isBitSet v_7668 12)));
      setRegister cf (notBool_ (isBitSet v_7668 0));
      setRegister of (bit_and (eq v_7676 (isBitSet v_7666 0)) (notBool_ (eq v_7676 v_7671)));
      setRegister pf (parityFlag (extract v_7668 9 17));
      setRegister sf v_7671;
      setRegister zf (zeroFlag (extract v_7668 1 17));
      pure ()
    pat_end;
    pattern fun (v_2479 : reg (bv 16)) (v_2478 : Mem) => do
      v_7695 <- getRegister v_2479;
      v_7699 <- evaluateAddress v_2478;
      v_7700 <- load v_7699 2;
      v_7702 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7695 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_7700));
      v_7705 <- eval (isBitSet v_7702 1);
      v_7710 <- eval (eq (bv_xor (extract v_7695 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_7695 v_7700) 11) (isBitSet v_7702 12)));
      setRegister cf (notBool_ (isBitSet v_7702 0));
      setRegister of (bit_and (eq v_7710 (isBitSet v_7700 0)) (notBool_ (eq v_7710 v_7705)));
      setRegister pf (parityFlag (extract v_7702 9 17));
      setRegister sf v_7705;
      setRegister zf (zeroFlag (extract v_7702 1 17));
      pure ()
    pat_end;
    pattern fun (v_2487 : Mem) (v_2488 : reg (bv 16)) => do
      v_7729 <- evaluateAddress v_2487;
      v_7730 <- load v_7729 2;
      v_7734 <- getRegister v_2488;
      v_7736 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7730 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_7734));
      v_7739 <- eval (isBitSet v_7736 1);
      v_7744 <- eval (eq (bv_xor (extract v_7730 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_7730 v_7734) 11) (isBitSet v_7736 12)));
      setRegister cf (notBool_ (isBitSet v_7736 0));
      setRegister of (bit_and (eq v_7744 (isBitSet v_7734 0)) (notBool_ (eq v_7744 v_7739)));
      setRegister pf (parityFlag (extract v_7736 9 17));
      setRegister sf v_7739;
      setRegister zf (zeroFlag (extract v_7736 1 17));
      pure ()
    pat_end
