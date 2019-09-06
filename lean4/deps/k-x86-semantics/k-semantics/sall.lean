def sall1 : instruction :=
  definst "sall" $ do
    pattern fun (_ : clReg) (v_3015 : reg (bv 32)) => do
      v_5529 <- getRegister rcx;
      v_5531 <- eval (bv_and (extract v_5529 56 64) (expression.bv_nat 8 31));
      v_5532 <- eval (eq v_5531 (expression.bv_nat 8 0));
      v_5533 <- getRegister zf;
      v_5534 <- getRegister v_3015;
      v_5538 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_5534) (concat (expression.bv_nat 25 0) v_5531)) 0 33);
      v_5539 <- eval (extract v_5538 1 33);
      v_5542 <- getRegister sf;
      v_5543 <- eval (isBitSet v_5538 1);
      v_5545 <- getRegister pf;
      v_5551 <- getRegister cf;
      v_5554 <- eval (mux (uge v_5531 (expression.bv_nat 8 32)) undef (mux v_5532 v_5551 (isBitSet v_5538 0)));
      v_5557 <- getRegister of;
      v_5560 <- getRegister af;
      setRegister (lhs.of_reg v_3015) v_5539;
      setRegister af (mux v_5532 v_5560 undef);
      setRegister cf v_5554;
      setRegister of (mux (eq v_5531 (expression.bv_nat 8 1)) (notBool_ (eq v_5554 v_5543)) (mux v_5532 v_5557 undef));
      setRegister pf (mux v_5532 v_5545 (parityFlag (extract v_5538 25 33)));
      setRegister sf (mux v_5532 v_5542 v_5543);
      setRegister zf (mux v_5532 v_5533 (eq v_5539 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_3017 : imm int) (v_3020 : reg (bv 32)) => do
      v_5570 <- eval (bv_and (handleImmediateWithSignExtend v_3017 8 8) (expression.bv_nat 8 31));
      v_5571 <- eval (eq v_5570 (expression.bv_nat 8 0));
      v_5572 <- getRegister zf;
      v_5573 <- getRegister v_3020;
      v_5577 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_5573) (concat (expression.bv_nat 25 0) v_5570)) 0 33);
      v_5578 <- eval (extract v_5577 1 33);
      v_5581 <- getRegister sf;
      v_5582 <- eval (isBitSet v_5577 1);
      v_5584 <- getRegister pf;
      v_5590 <- getRegister cf;
      v_5593 <- eval (mux (uge v_5570 (expression.bv_nat 8 32)) undef (mux v_5571 v_5590 (isBitSet v_5577 0)));
      v_5596 <- getRegister of;
      v_5599 <- getRegister af;
      setRegister (lhs.of_reg v_3020) v_5578;
      setRegister af (mux v_5571 v_5599 undef);
      setRegister cf v_5593;
      setRegister of (mux (eq v_5570 (expression.bv_nat 8 1)) (notBool_ (eq v_5593 v_5582)) (mux v_5571 v_5596 undef));
      setRegister pf (mux v_5571 v_5584 (parityFlag (extract v_5577 25 33)));
      setRegister sf (mux v_5571 v_5581 v_5582);
      setRegister zf (mux v_5571 v_5572 (eq v_5578 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_3024 : reg (bv 32)) => do
      v_7521 <- getRegister v_3024;
      v_7524 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_7521) (expression.bv_nat 33 1)) 0 33);
      v_7525 <- eval (extract v_7524 1 33);
      v_7527 <- eval (isBitSet v_7524 1);
      v_7530 <- eval (isBitSet v_7524 0);
      setRegister (lhs.of_reg v_3024) v_7525;
      setRegister af undef;
      setRegister cf v_7530;
      setRegister of (notBool_ (eq v_7530 v_7527));
      setRegister pf (parityFlag (extract v_7524 25 33));
      setRegister sf v_7527;
      setRegister zf (zeroFlag v_7525);
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_3000 : Mem) => do
      v_11975 <- evaluateAddress v_3000;
      v_11976 <- load v_11975 4;
      v_11978 <- getRegister rcx;
      v_11980 <- eval (bv_and (extract v_11978 56 64) (expression.bv_nat 8 31));
      v_11983 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_11976) (concat (expression.bv_nat 25 0) v_11980)) 0 33);
      v_11984 <- eval (extract v_11983 1 33);
      store v_11975 v_11984 4;
      v_11986 <- eval (eq v_11980 (expression.bv_nat 8 0));
      v_11987 <- getRegister zf;
      v_11990 <- getRegister sf;
      v_11991 <- eval (isBitSet v_11983 1);
      v_11993 <- getRegister pf;
      v_11999 <- getRegister cf;
      v_12002 <- eval (mux (uge v_11980 (expression.bv_nat 8 32)) undef (mux v_11986 v_11999 (isBitSet v_11983 0)));
      v_12005 <- getRegister of;
      v_12008 <- getRegister af;
      setRegister af (mux v_11986 v_12008 undef);
      setRegister cf v_12002;
      setRegister of (mux (eq v_11980 (expression.bv_nat 8 1)) (notBool_ (eq v_12002 v_11991)) (mux v_11986 v_12005 undef));
      setRegister pf (mux v_11986 v_11993 (parityFlag (extract v_11983 25 33)));
      setRegister sf (mux v_11986 v_11990 v_11991);
      setRegister zf (mux v_11986 v_11987 (eq v_11984 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_3003 : imm int) (v_3004 : Mem) => do
      v_12016 <- evaluateAddress v_3004;
      v_12017 <- load v_12016 4;
      v_12020 <- eval (bv_and (handleImmediateWithSignExtend v_3003 8 8) (expression.bv_nat 8 31));
      v_12023 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_12017) (concat (expression.bv_nat 25 0) v_12020)) 0 33);
      v_12024 <- eval (extract v_12023 1 33);
      store v_12016 v_12024 4;
      v_12026 <- eval (eq v_12020 (expression.bv_nat 8 0));
      v_12027 <- getRegister zf;
      v_12030 <- getRegister sf;
      v_12031 <- eval (isBitSet v_12023 1);
      v_12033 <- getRegister pf;
      v_12039 <- getRegister cf;
      v_12042 <- eval (mux (uge v_12020 (expression.bv_nat 8 32)) undef (mux v_12026 v_12039 (isBitSet v_12023 0)));
      v_12045 <- getRegister of;
      v_12048 <- getRegister af;
      setRegister af (mux v_12026 v_12048 undef);
      setRegister cf v_12042;
      setRegister of (mux (eq v_12020 (expression.bv_nat 8 1)) (notBool_ (eq v_12042 v_12031)) (mux v_12026 v_12045 undef));
      setRegister pf (mux v_12026 v_12033 (parityFlag (extract v_12023 25 33)));
      setRegister sf (mux v_12026 v_12030 v_12031);
      setRegister zf (mux v_12026 v_12027 (eq v_12024 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_3009 : Mem) => do
      v_13134 <- evaluateAddress v_3009;
      v_13135 <- load v_13134 4;
      v_13138 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_13135) (expression.bv_nat 33 1)) 0 33);
      v_13139 <- eval (extract v_13138 1 33);
      store v_13134 v_13139 4;
      v_13142 <- eval (isBitSet v_13138 1);
      v_13145 <- eval (isBitSet v_13138 0);
      setRegister af undef;
      setRegister cf v_13145;
      setRegister of (notBool_ (eq v_13145 v_13142));
      setRegister pf (parityFlag (extract v_13138 25 33));
      setRegister sf v_13142;
      setRegister zf (zeroFlag v_13139);
      pure ()
    pat_end
