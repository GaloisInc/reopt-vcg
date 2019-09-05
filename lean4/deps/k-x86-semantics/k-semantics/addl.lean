def addl1 : instruction :=
  definst "addl" $ do
    pattern fun (v_2642 : imm int) (v_2643 : reg (bv 32)) => do
      v_4675 <- eval (handleImmediateWithSignExtend v_2642 32 32);
      v_4677 <- getRegister v_2643;
      v_4679 <- eval (add (concat (expression.bv_nat 1 0) v_4675) (concat (expression.bv_nat 1 0) v_4677));
      v_4680 <- eval (extract v_4679 1 33);
      v_4682 <- eval (isBitSet v_4679 1);
      v_4685 <- eval (isBitSet v_4675 0);
      setRegister (lhs.of_reg v_2643) v_4680;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4675 v_4677) 27) (isBitSet v_4679 28)));
      setRegister cf (isBitSet v_4679 0);
      setRegister of (bit_and (eq v_4685 (isBitSet v_4677 0)) (notBool_ (eq v_4685 v_4682)));
      setRegister pf (parityFlag (extract v_4679 25 33));
      setRegister sf v_4682;
      setRegister zf (zeroFlag v_4680);
      pure ()
    pat_end;
    pattern fun (v_2651 : reg (bv 32)) (v_2652 : reg (bv 32)) => do
      v_4708 <- getRegister v_2651;
      v_4710 <- getRegister v_2652;
      v_4712 <- eval (add (concat (expression.bv_nat 1 0) v_4708) (concat (expression.bv_nat 1 0) v_4710));
      v_4713 <- eval (extract v_4712 1 33);
      v_4715 <- eval (isBitSet v_4712 1);
      v_4718 <- eval (isBitSet v_4708 0);
      setRegister (lhs.of_reg v_2652) v_4713;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4708 v_4710) 27) (isBitSet v_4712 28)));
      setRegister cf (isBitSet v_4712 0);
      setRegister of (bit_and (eq v_4718 (isBitSet v_4710 0)) (notBool_ (eq v_4718 v_4715)));
      setRegister pf (parityFlag (extract v_4712 25 33));
      setRegister sf v_4715;
      setRegister zf (zeroFlag v_4713);
      pure ()
    pat_end;
    pattern fun (v_2648 : Mem) (v_2647 : reg (bv 32)) => do
      v_8886 <- evaluateAddress v_2648;
      v_8887 <- load v_8886 4;
      v_8889 <- getRegister v_2647;
      v_8891 <- eval (add (concat (expression.bv_nat 1 0) v_8887) (concat (expression.bv_nat 1 0) v_8889));
      v_8892 <- eval (extract v_8891 1 33);
      v_8894 <- eval (isBitSet v_8891 1);
      v_8897 <- eval (isBitSet v_8887 0);
      setRegister (lhs.of_reg v_2647) v_8892;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8887 v_8889) 27) (isBitSet v_8891 28)));
      setRegister cf (isBitSet v_8891 0);
      setRegister of (bit_and (eq v_8897 (isBitSet v_8889 0)) (notBool_ (eq v_8897 v_8894)));
      setRegister pf (parityFlag (extract v_8891 25 33));
      setRegister sf v_8894;
      setRegister zf (zeroFlag v_8892);
      pure ()
    pat_end;
    pattern fun (v_2634 : imm int) (v_2635 : Mem) => do
      v_10377 <- evaluateAddress v_2635;
      v_10378 <- eval (handleImmediateWithSignExtend v_2634 32 32);
      v_10380 <- load v_10377 4;
      v_10382 <- eval (add (concat (expression.bv_nat 1 0) v_10378) (concat (expression.bv_nat 1 0) v_10380));
      v_10383 <- eval (extract v_10382 1 33);
      store v_10377 v_10383 4;
      v_10386 <- eval (isBitSet v_10382 1);
      v_10389 <- eval (isBitSet v_10378 0);
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10378 v_10380) 27) (isBitSet v_10382 28)));
      setRegister cf (isBitSet v_10382 0);
      setRegister of (bit_and (eq v_10389 (isBitSet v_10380 0)) (notBool_ (eq v_10389 v_10386)));
      setRegister pf (parityFlag (extract v_10382 25 33));
      setRegister sf v_10386;
      setRegister zf (zeroFlag v_10383);
      pure ()
    pat_end;
    pattern fun (v_2638 : reg (bv 32)) (v_2639 : Mem) => do
      v_10407 <- evaluateAddress v_2639;
      v_10408 <- getRegister v_2638;
      v_10410 <- load v_10407 4;
      v_10412 <- eval (add (concat (expression.bv_nat 1 0) v_10408) (concat (expression.bv_nat 1 0) v_10410));
      v_10413 <- eval (extract v_10412 1 33);
      store v_10407 v_10413 4;
      v_10416 <- eval (isBitSet v_10412 1);
      v_10419 <- eval (isBitSet v_10408 0);
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10408 v_10410) 27) (isBitSet v_10412 28)));
      setRegister cf (isBitSet v_10412 0);
      setRegister of (bit_and (eq v_10419 (isBitSet v_10410 0)) (notBool_ (eq v_10419 v_10416)));
      setRegister pf (parityFlag (extract v_10412 25 33));
      setRegister sf v_10416;
      setRegister zf (zeroFlag v_10413);
      pure ()
    pat_end
