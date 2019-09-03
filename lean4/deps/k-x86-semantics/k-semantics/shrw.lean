def shrw1 : instruction :=
  definst "shrw" $ do
    pattern fun cl (v_2973 : reg (bv 16)) => do
      v_6404 <- getRegister rcx;
      v_6406 <- eval (bv_and (extract v_6404 56 64) (expression.bv_nat 8 31));
      v_6407 <- eval (uge v_6406 (expression.bv_nat 8 16));
      v_6410 <- eval (eq v_6406 (expression.bv_nat 8 0));
      v_6411 <- eval (notBool_ v_6410);
      v_6412 <- getRegister v_2973;
      v_6416 <- eval (lshr (concat v_6412 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 9 0) v_6406)));
      v_6420 <- getRegister cf;
      v_6430 <- getRegister sf;
      v_6435 <- eval (bit_and v_6411 undef);
      v_6436 <- getRegister af;
      v_6441 <- eval (extract v_6416 0 16);
      v_6444 <- getRegister zf;
      v_6479 <- getRegister pf;
      v_6484 <- eval (eq v_6406 (expression.bv_nat 8 1));
      v_6489 <- getRegister of;
      setRegister (lhs.of_reg v_2973) v_6441;
      setRegister of (mux (bit_or (bit_and v_6484 (eq (extract v_6412 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_6484) (bit_or v_6435 (bit_and v_6410 (eq v_6489 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_6411 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_6416 15 16) (expression.bv_nat 1 1)) (eq (extract v_6416 14 15) (expression.bv_nat 1 1)))) (eq (extract v_6416 13 14) (expression.bv_nat 1 1)))) (eq (extract v_6416 12 13) (expression.bv_nat 1 1)))) (eq (extract v_6416 11 12) (expression.bv_nat 1 1)))) (eq (extract v_6416 10 11) (expression.bv_nat 1 1)))) (eq (extract v_6416 9 10) (expression.bv_nat 1 1)))) (eq (extract v_6416 8 9) (expression.bv_nat 1 1)))) (bit_and v_6410 (eq v_6479 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_6411 (eq v_6441 (expression.bv_nat 16 0))) (bit_and v_6410 (eq v_6444 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_6435 (bit_and v_6410 (eq v_6436 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_6411 (eq (extract v_6416 0 1) (expression.bv_nat 1 1))) (bit_and v_6410 (eq v_6430 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_6407 undef) (bit_and (notBool_ v_6407) (bit_or (bit_and v_6411 (eq (extract v_6416 16 17) (expression.bv_nat 1 1))) (bit_and v_6410 (eq v_6420 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2976 : imm int) (v_2978 : reg (bv 16)) => do
      v_6504 <- eval (bv_and (handleImmediateWithSignExtend v_2976 8 8) (expression.bv_nat 8 31));
      v_6505 <- eval (uge v_6504 (expression.bv_nat 8 16));
      v_6508 <- eval (eq v_6504 (expression.bv_nat 8 0));
      v_6509 <- eval (notBool_ v_6508);
      v_6510 <- getRegister v_2978;
      v_6514 <- eval (lshr (concat v_6510 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 9 0) v_6504)));
      v_6518 <- getRegister cf;
      v_6528 <- getRegister sf;
      v_6533 <- eval (bit_and v_6509 undef);
      v_6534 <- getRegister af;
      v_6539 <- eval (extract v_6514 0 16);
      v_6542 <- getRegister zf;
      v_6577 <- getRegister pf;
      v_6582 <- eval (eq v_6504 (expression.bv_nat 8 1));
      v_6587 <- getRegister of;
      setRegister (lhs.of_reg v_2978) v_6539;
      setRegister of (mux (bit_or (bit_and v_6582 (eq (extract v_6510 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_6582) (bit_or v_6533 (bit_and v_6508 (eq v_6587 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_6509 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_6514 15 16) (expression.bv_nat 1 1)) (eq (extract v_6514 14 15) (expression.bv_nat 1 1)))) (eq (extract v_6514 13 14) (expression.bv_nat 1 1)))) (eq (extract v_6514 12 13) (expression.bv_nat 1 1)))) (eq (extract v_6514 11 12) (expression.bv_nat 1 1)))) (eq (extract v_6514 10 11) (expression.bv_nat 1 1)))) (eq (extract v_6514 9 10) (expression.bv_nat 1 1)))) (eq (extract v_6514 8 9) (expression.bv_nat 1 1)))) (bit_and v_6508 (eq v_6577 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_6509 (eq v_6539 (expression.bv_nat 16 0))) (bit_and v_6508 (eq v_6542 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_6533 (bit_and v_6508 (eq v_6534 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_6509 (eq (extract v_6514 0 1) (expression.bv_nat 1 1))) (bit_and v_6508 (eq v_6528 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_6505 undef) (bit_and (notBool_ v_6505) (bit_or (bit_and v_6509 (eq (extract v_6514 16 17) (expression.bv_nat 1 1))) (bit_and v_6508 (eq v_6518 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2985 : reg (bv 16)) => do
      v_6603 <- getRegister v_2985;
      v_6605 <- eval (lshr (concat v_6603 (expression.bv_nat 1 0)) 1);
      v_6608 <- eval (extract v_6605 0 16);
      setRegister (lhs.of_reg v_2985) v_6608;
      setRegister of (extract v_6603 0 1);
      setRegister pf (parityFlag (extract v_6605 8 16));
      setRegister zf (zeroFlag v_6608);
      setRegister af undef;
      setRegister sf (extract v_6605 0 1);
      setRegister cf (extract v_6605 16 17);
      pure ()
    pat_end;
    pattern fun (v_2981 : reg (bv 16)) => do
      v_8115 <- getRegister v_2981;
      v_8117 <- eval (lshr (concat v_8115 (expression.bv_nat 1 0)) 1);
      v_8124 <- eval (extract v_8117 0 16);
      setRegister (lhs.of_reg v_2981) v_8124;
      setRegister of (mux (eq (extract v_8115 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8117 8 16));
      setRegister zf (zeroFlag v_8124);
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (eq (extract v_8117 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_8117 16 17) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2981 : reg (bv 16)) => do
      v_8138 <- getRegister v_2981;
      v_8140 <- eval (lshr (concat v_8138 (expression.bv_nat 1 0)) 1);
      v_8143 <- eval (extract v_8140 0 16);
      setRegister (lhs.of_reg v_2981) v_8143;
      setRegister of (extract v_8138 0 1);
      setRegister pf (parityFlag (extract v_8140 8 16));
      setRegister zf (zeroFlag v_8143);
      setRegister af undef;
      setRegister sf (extract v_8140 0 1);
      setRegister cf (extract v_8140 16 17);
      pure ()
    pat_end;
    pattern fun cl (v_2959 : Mem) => do
      v_12646 <- evaluateAddress v_2959;
      v_12647 <- load v_12646 2;
      v_12649 <- getRegister rcx;
      v_12651 <- eval (bv_and (extract v_12649 56 64) (expression.bv_nat 8 31));
      v_12654 <- eval (lshr (concat v_12647 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 9 0) v_12651)));
      v_12655 <- eval (extract v_12654 0 16);
      store v_12646 v_12655 2;
      v_12657 <- eval (uge v_12651 (expression.bv_nat 8 16));
      v_12660 <- eval (eq v_12651 (expression.bv_nat 8 0));
      v_12661 <- eval (notBool_ v_12660);
      v_12665 <- getRegister cf;
      v_12675 <- getRegister sf;
      v_12682 <- getRegister zf;
      v_12687 <- eval (bit_and v_12661 undef);
      v_12688 <- getRegister af;
      v_12723 <- getRegister pf;
      v_12728 <- eval (eq v_12651 (expression.bv_nat 8 1));
      v_12733 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_12728 (eq (extract v_12647 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_12728) (bit_or v_12687 (bit_and v_12660 (eq v_12733 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_12661 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_12654 15 16) (expression.bv_nat 1 1)) (eq (extract v_12654 14 15) (expression.bv_nat 1 1)))) (eq (extract v_12654 13 14) (expression.bv_nat 1 1)))) (eq (extract v_12654 12 13) (expression.bv_nat 1 1)))) (eq (extract v_12654 11 12) (expression.bv_nat 1 1)))) (eq (extract v_12654 10 11) (expression.bv_nat 1 1)))) (eq (extract v_12654 9 10) (expression.bv_nat 1 1)))) (eq (extract v_12654 8 9) (expression.bv_nat 1 1)))) (bit_and v_12660 (eq v_12723 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_12687 (bit_and v_12660 (eq v_12688 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_12661 (eq v_12655 (expression.bv_nat 16 0))) (bit_and v_12660 (eq v_12682 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_12661 (eq (extract v_12654 0 1) (expression.bv_nat 1 1))) (bit_and v_12660 (eq v_12675 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_12657 undef) (bit_and (notBool_ v_12657) (bit_or (bit_and v_12661 (eq (extract v_12654 16 17) (expression.bv_nat 1 1))) (bit_and v_12660 (eq v_12665 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2962 : imm int) (v_2963 : Mem) => do
      v_12746 <- evaluateAddress v_2963;
      v_12747 <- load v_12746 2;
      v_12750 <- eval (bv_and (handleImmediateWithSignExtend v_2962 8 8) (expression.bv_nat 8 31));
      v_12753 <- eval (lshr (concat v_12747 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 9 0) v_12750)));
      v_12754 <- eval (extract v_12753 0 16);
      store v_12746 v_12754 2;
      v_12756 <- eval (uge v_12750 (expression.bv_nat 8 16));
      v_12759 <- eval (eq v_12750 (expression.bv_nat 8 0));
      v_12760 <- eval (notBool_ v_12759);
      v_12764 <- getRegister cf;
      v_12774 <- getRegister sf;
      v_12781 <- getRegister zf;
      v_12786 <- eval (bit_and v_12760 undef);
      v_12787 <- getRegister af;
      v_12822 <- getRegister pf;
      v_12827 <- eval (eq v_12750 (expression.bv_nat 8 1));
      v_12832 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_12827 (eq (extract v_12747 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_12827) (bit_or v_12786 (bit_and v_12759 (eq v_12832 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_12760 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_12753 15 16) (expression.bv_nat 1 1)) (eq (extract v_12753 14 15) (expression.bv_nat 1 1)))) (eq (extract v_12753 13 14) (expression.bv_nat 1 1)))) (eq (extract v_12753 12 13) (expression.bv_nat 1 1)))) (eq (extract v_12753 11 12) (expression.bv_nat 1 1)))) (eq (extract v_12753 10 11) (expression.bv_nat 1 1)))) (eq (extract v_12753 9 10) (expression.bv_nat 1 1)))) (eq (extract v_12753 8 9) (expression.bv_nat 1 1)))) (bit_and v_12759 (eq v_12822 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_12786 (bit_and v_12759 (eq v_12787 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_12760 (eq v_12754 (expression.bv_nat 16 0))) (bit_and v_12759 (eq v_12781 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_12760 (eq (extract v_12753 0 1) (expression.bv_nat 1 1))) (bit_and v_12759 (eq v_12774 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_12756 undef) (bit_and (notBool_ v_12756) (bit_or (bit_and v_12760 (eq (extract v_12753 16 17) (expression.bv_nat 1 1))) (bit_and v_12759 (eq v_12764 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2966 : Mem) => do
      v_13460 <- evaluateAddress v_2966;
      v_13461 <- load v_13460 2;
      v_13463 <- eval (lshr (concat v_13461 (expression.bv_nat 1 0)) 1);
      v_13464 <- eval (extract v_13463 0 16);
      store v_13460 v_13464 2;
      setRegister of (mux (eq (extract v_13461 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_13463 8 16));
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_13464);
      setRegister sf (mux (eq (extract v_13463 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_13463 16 17) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2966 : Mem) => do
      v_13484 <- evaluateAddress v_2966;
      v_13485 <- load v_13484 2;
      v_13487 <- eval (lshr (concat v_13485 (expression.bv_nat 1 0)) 1);
      v_13488 <- eval (extract v_13487 0 16);
      store v_13484 v_13488 2;
      setRegister of (extract v_13485 0 1);
      setRegister pf (parityFlag (extract v_13487 8 16));
      setRegister af undef;
      setRegister zf (zeroFlag v_13488);
      setRegister sf (extract v_13487 0 1);
      setRegister cf (extract v_13487 16 17);
      pure ()
    pat_end
