def addl1 : instruction :=
  definst "addl" $ do
    pattern fun (v_2566 : imm int) eax => do
      v_4636 <- eval (handleImmediateWithSignExtend v_2566 32 32);
      v_4638 <- getRegister rax;
      v_4641 <- eval (add (concat (expression.bv_nat 1 0) v_4636) (concat (expression.bv_nat 1 0) (extract v_4638 32 64)));
      v_4643 <- eval (extract v_4641 1 2);
      v_4649 <- eval (extract v_4641 1 33);
      v_4654 <- eval (eq (extract v_4636 0 1) (expression.bv_nat 1 1));
      setRegister eax v_4649;
      setRegister of (mux (bit_and (eq v_4654 (eq (extract v_4638 32 33) (expression.bv_nat 1 1))) (notBool_ (eq v_4654 (eq v_4643 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4641 25 33));
      setRegister zf (zeroFlag v_4649);
      setRegister af (bv_xor (bv_xor (extract v_4636 27 28) (extract v_4638 59 60)) (extract v_4641 28 29));
      setRegister sf v_4643;
      setRegister cf (extract v_4641 0 1);
      pure ()
    pat_end;
    pattern fun (v_2578 : imm int) (v_2580 : reg (bv 32)) => do
      v_4678 <- eval (handleImmediateWithSignExtend v_2578 32 32);
      v_4680 <- getRegister v_2580;
      v_4682 <- eval (add (concat (expression.bv_nat 1 0) v_4678) (concat (expression.bv_nat 1 0) v_4680));
      v_4684 <- eval (extract v_4682 1 2);
      v_4685 <- eval (extract v_4682 1 33);
      v_4694 <- eval (eq (extract v_4678 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2580) v_4685;
      setRegister of (mux (bit_and (eq v_4694 (eq (extract v_4680 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4694 (eq v_4684 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4682 25 33));
      setRegister af (bv_xor (extract (bv_xor v_4678 v_4680) 27 28) (extract v_4682 28 29));
      setRegister zf (zeroFlag v_4685);
      setRegister sf v_4684;
      setRegister cf (extract v_4682 0 1);
      pure ()
    pat_end;
    pattern fun (v_2588 : reg (bv 32)) (v_2589 : reg (bv 32)) => do
      v_4714 <- getRegister v_2588;
      v_4716 <- getRegister v_2589;
      v_4718 <- eval (add (concat (expression.bv_nat 1 0) v_4714) (concat (expression.bv_nat 1 0) v_4716));
      v_4720 <- eval (extract v_4718 1 2);
      v_4721 <- eval (extract v_4718 1 33);
      v_4730 <- eval (eq (extract v_4714 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2589) v_4721;
      setRegister of (mux (bit_and (eq v_4730 (eq (extract v_4716 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4730 (eq v_4720 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4718 25 33));
      setRegister af (bv_xor (extract (bv_xor v_4714 v_4716) 27 28) (extract v_4718 28 29));
      setRegister zf (zeroFlag v_4721);
      setRegister sf v_4720;
      setRegister cf (extract v_4718 0 1);
      pure ()
    pat_end;
    pattern fun (v_2583 : Mem) (v_2584 : reg (bv 32)) => do
      v_9068 <- evaluateAddress v_2583;
      v_9069 <- load v_9068 4;
      v_9071 <- getRegister v_2584;
      v_9073 <- eval (add (concat (expression.bv_nat 1 0) v_9069) (concat (expression.bv_nat 1 0) v_9071));
      v_9075 <- eval (extract v_9073 1 2);
      v_9076 <- eval (extract v_9073 1 33);
      v_9085 <- eval (eq (extract v_9069 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2584) v_9076;
      setRegister of (mux (bit_and (eq v_9085 (eq (extract v_9071 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_9085 (eq v_9075 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9073 25 33));
      setRegister af (bv_xor (extract (bv_xor v_9069 v_9071) 27 28) (extract v_9073 28 29));
      setRegister zf (zeroFlag v_9076);
      setRegister sf v_9075;
      setRegister cf (extract v_9073 0 1);
      pure ()
    pat_end;
    pattern fun (v_2571 : imm int) (v_2570 : Mem) => do
      v_10668 <- evaluateAddress v_2570;
      v_10669 <- eval (handleImmediateWithSignExtend v_2571 32 32);
      v_10671 <- load v_10668 4;
      v_10673 <- eval (add (concat (expression.bv_nat 1 0) v_10669) (concat (expression.bv_nat 1 0) v_10671));
      v_10674 <- eval (extract v_10673 1 33);
      store v_10668 v_10674 4;
      v_10677 <- eval (extract v_10673 1 2);
      v_10686 <- eval (eq (extract v_10669 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10686 (eq (extract v_10671 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10686 (eq v_10677 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10673 25 33));
      setRegister af (bv_xor (extract (bv_xor v_10669 v_10671) 27 28) (extract v_10673 28 29));
      setRegister zf (zeroFlag v_10674);
      setRegister sf v_10677;
      setRegister cf (extract v_10673 0 1);
      pure ()
    pat_end;
    pattern fun (v_2575 : reg (bv 32)) (v_2574 : Mem) => do
      v_10701 <- evaluateAddress v_2574;
      v_10702 <- getRegister v_2575;
      v_10704 <- load v_10701 4;
      v_10706 <- eval (add (concat (expression.bv_nat 1 0) v_10702) (concat (expression.bv_nat 1 0) v_10704));
      v_10707 <- eval (extract v_10706 1 33);
      store v_10701 v_10707 4;
      v_10710 <- eval (extract v_10706 1 2);
      v_10719 <- eval (eq (extract v_10702 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10719 (eq (extract v_10704 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10719 (eq v_10710 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10706 25 33));
      setRegister af (bv_xor (extract (bv_xor v_10702 v_10704) 27 28) (extract v_10706 28 29));
      setRegister zf (zeroFlag v_10707);
      setRegister sf v_10710;
      setRegister cf (extract v_10706 0 1);
      pure ()
    pat_end
