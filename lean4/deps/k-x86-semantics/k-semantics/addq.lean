def addq1 : instruction :=
  definst "addq" $ do
    pattern fun (v_2682 : imm int) (v_2684 : reg (bv 64)) => do
      v_4799 <- eval (handleImmediateWithSignExtend v_2682 32 32);
      v_4800 <- eval (sext v_4799 64);
      v_4802 <- getRegister v_2684;
      v_4804 <- eval (add (concat (expression.bv_nat 1 0) v_4800) (concat (expression.bv_nat 1 0) v_4802));
      v_4805 <- eval (extract v_4804 1 65);
      v_4807 <- eval (isBitSet v_4804 1);
      v_4810 <- eval (isBitSet v_4800 0);
      setRegister (lhs.of_reg v_2684) v_4805;
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_4799 27) (isBitSet v_4802 59))) (isBitSet v_4804 60)));
      setRegister cf (isBitSet v_4804 0);
      setRegister of (bit_and (eq v_4810 (isBitSet v_4802 0)) (notBool_ (eq v_4810 v_4807)));
      setRegister pf (parityFlag (extract v_4804 57 65));
      setRegister sf v_4807;
      setRegister zf (zeroFlag v_4805);
      pure ()
    pat_end;
    pattern fun (v_2692 : reg (bv 64)) (v_2693 : reg (bv 64)) => do
      v_4835 <- getRegister v_2692;
      v_4837 <- getRegister v_2693;
      v_4839 <- eval (add (concat (expression.bv_nat 1 0) v_4835) (concat (expression.bv_nat 1 0) v_4837));
      v_4840 <- eval (extract v_4839 1 65);
      v_4842 <- eval (isBitSet v_4839 1);
      v_4845 <- eval (isBitSet v_4835 0);
      setRegister (lhs.of_reg v_2693) v_4840;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4835 v_4837) 59) (isBitSet v_4839 60)));
      setRegister cf (isBitSet v_4839 0);
      setRegister of (bit_and (eq v_4845 (isBitSet v_4837 0)) (notBool_ (eq v_4845 v_4842)));
      setRegister pf (parityFlag (extract v_4839 57 65));
      setRegister sf v_4842;
      setRegister zf (zeroFlag v_4840);
      pure ()
    pat_end;
    pattern fun (v_2687 : Mem) (v_2688 : reg (bv 64)) => do
      v_8966 <- evaluateAddress v_2687;
      v_8967 <- load v_8966 8;
      v_8969 <- getRegister v_2688;
      v_8971 <- eval (add (concat (expression.bv_nat 1 0) v_8967) (concat (expression.bv_nat 1 0) v_8969));
      v_8972 <- eval (extract v_8971 1 65);
      v_8974 <- eval (isBitSet v_8971 1);
      v_8977 <- eval (isBitSet v_8967 0);
      setRegister (lhs.of_reg v_2688) v_8972;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8967 v_8969) 59) (isBitSet v_8971 60)));
      setRegister cf (isBitSet v_8971 0);
      setRegister of (bit_and (eq v_8977 (isBitSet v_8969 0)) (notBool_ (eq v_8977 v_8974)));
      setRegister pf (parityFlag (extract v_8971 57 65));
      setRegister sf v_8974;
      setRegister zf (zeroFlag v_8972);
      pure ()
    pat_end;
    pattern fun (v_2674 : imm int) (v_2675 : Mem) => do
      v_10437 <- evaluateAddress v_2675;
      v_10438 <- eval (handleImmediateWithSignExtend v_2674 32 32);
      v_10439 <- eval (sext v_10438 64);
      v_10441 <- load v_10437 8;
      v_10443 <- eval (add (concat (expression.bv_nat 1 0) v_10439) (concat (expression.bv_nat 1 0) v_10441));
      v_10444 <- eval (extract v_10443 1 65);
      store v_10437 v_10444 8;
      v_10447 <- eval (isBitSet v_10443 1);
      v_10450 <- eval (isBitSet v_10439 0);
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_10438 27) (isBitSet v_10441 59))) (isBitSet v_10443 60)));
      setRegister cf (isBitSet v_10443 0);
      setRegister of (bit_and (eq v_10450 (isBitSet v_10441 0)) (notBool_ (eq v_10450 v_10447)));
      setRegister pf (parityFlag (extract v_10443 57 65));
      setRegister sf v_10447;
      setRegister zf (zeroFlag v_10444);
      pure ()
    pat_end;
    pattern fun (v_2679 : reg (bv 64)) (v_2678 : Mem) => do
      v_10470 <- evaluateAddress v_2678;
      v_10471 <- getRegister v_2679;
      v_10473 <- load v_10470 8;
      v_10475 <- eval (add (concat (expression.bv_nat 1 0) v_10471) (concat (expression.bv_nat 1 0) v_10473));
      v_10476 <- eval (extract v_10475 1 65);
      store v_10470 v_10476 8;
      v_10479 <- eval (isBitSet v_10475 1);
      v_10482 <- eval (isBitSet v_10471 0);
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10471 v_10473) 59) (isBitSet v_10475 60)));
      setRegister cf (isBitSet v_10475 0);
      setRegister of (bit_and (eq v_10482 (isBitSet v_10473 0)) (notBool_ (eq v_10482 v_10479)));
      setRegister pf (parityFlag (extract v_10475 57 65));
      setRegister sf v_10479;
      setRegister zf (zeroFlag v_10476);
      pure ()
    pat_end
