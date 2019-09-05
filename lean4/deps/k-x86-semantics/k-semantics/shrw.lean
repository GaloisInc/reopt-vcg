def shrw1 : instruction :=
  definst "shrw" $ do
    pattern fun cl (v_3037 : reg (bv 16)) => do
      v_5782 <- getRegister rcx;
      v_5784 <- eval (bv_and (extract v_5782 56 64) (expression.bv_nat 8 31));
      v_5785 <- eval (eq v_5784 (expression.bv_nat 8 0));
      v_5786 <- eval (notBool_ v_5785);
      v_5787 <- getRegister v_3037;
      v_5790 <- eval (lshr (concat v_5787 (expression.bv_nat 1 0)) (concat (expression.bv_nat 9 0) v_5784));
      v_5791 <- eval (extract v_5790 0 16);
      v_5794 <- getRegister zf;
      v_5800 <- getRegister sf;
      v_5807 <- getRegister pf;
      v_5811 <- eval (eq v_5784 (expression.bv_nat 8 1));
      v_5815 <- eval (bit_and v_5786 undef);
      v_5816 <- getRegister of;
      v_5822 <- eval (uge v_5784 (expression.bv_nat 8 16));
      v_5827 <- getRegister cf;
      v_5833 <- getRegister af;
      setRegister (lhs.of_reg v_3037) v_5791;
      setRegister af (bit_or v_5815 (bit_and v_5785 (eq v_5833 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_5822 undef) (bit_and (notBool_ v_5822) (bit_or (bit_and v_5786 (isBitSet v_5790 16)) (bit_and v_5785 (eq v_5827 (expression.bv_nat 1 1))))));
      setRegister of (bit_or (bit_and v_5811 (isBitSet v_5787 0)) (bit_and (notBool_ v_5811) (bit_or v_5815 (bit_and v_5785 (eq v_5816 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_5786 (parityFlag (extract v_5790 8 16))) (bit_and v_5785 (eq v_5807 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_5786 (isBitSet v_5790 0)) (bit_and v_5785 (eq v_5800 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_5786 (eq v_5791 (expression.bv_nat 16 0))) (bit_and v_5785 (eq v_5794 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3040 : imm int) (v_3042 : reg (bv 16)) => do
      v_5845 <- eval (bv_and (handleImmediateWithSignExtend v_3040 8 8) (expression.bv_nat 8 31));
      v_5846 <- eval (eq v_5845 (expression.bv_nat 8 0));
      v_5847 <- eval (notBool_ v_5846);
      v_5848 <- getRegister v_3042;
      v_5851 <- eval (lshr (concat v_5848 (expression.bv_nat 1 0)) (concat (expression.bv_nat 9 0) v_5845));
      v_5852 <- eval (extract v_5851 0 16);
      v_5855 <- getRegister zf;
      v_5861 <- getRegister sf;
      v_5868 <- getRegister pf;
      v_5872 <- eval (eq v_5845 (expression.bv_nat 8 1));
      v_5876 <- eval (bit_and v_5847 undef);
      v_5877 <- getRegister of;
      v_5883 <- eval (uge v_5845 (expression.bv_nat 8 16));
      v_5888 <- getRegister cf;
      v_5894 <- getRegister af;
      setRegister (lhs.of_reg v_3042) v_5852;
      setRegister af (bit_or v_5876 (bit_and v_5846 (eq v_5894 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_5883 undef) (bit_and (notBool_ v_5883) (bit_or (bit_and v_5847 (isBitSet v_5851 16)) (bit_and v_5846 (eq v_5888 (expression.bv_nat 1 1))))));
      setRegister of (bit_or (bit_and v_5872 (isBitSet v_5848 0)) (bit_and (notBool_ v_5872) (bit_or v_5876 (bit_and v_5846 (eq v_5877 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_5847 (parityFlag (extract v_5851 8 16))) (bit_and v_5846 (eq v_5868 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_5847 (isBitSet v_5851 0)) (bit_and v_5846 (eq v_5861 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_5847 (eq v_5852 (expression.bv_nat 16 0))) (bit_and v_5846 (eq v_5855 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3045 : reg (bv 16)) => do
      v_7187 <- getRegister v_3045;
      v_7189 <- eval (lshr (concat v_7187 (expression.bv_nat 1 0)) (expression.bv_nat 17 1));
      v_7190 <- eval (extract v_7189 0 16);
      setRegister (lhs.of_reg v_3045) v_7190;
      setRegister af undef;
      setRegister cf (isBitSet v_7189 16);
      setRegister of (isBitSet v_7187 0);
      setRegister pf (parityFlag (extract v_7189 8 16));
      setRegister sf (isBitSet v_7189 0);
      setRegister zf (zeroFlag v_7190);
      pure ()
    pat_end;
    pattern fun cl (v_3023 : Mem) => do
      v_10600 <- evaluateAddress v_3023;
      v_10601 <- load v_10600 2;
      v_10603 <- getRegister rcx;
      v_10605 <- eval (bv_and (extract v_10603 56 64) (expression.bv_nat 8 31));
      v_10607 <- eval (lshr (concat v_10601 (expression.bv_nat 1 0)) (concat (expression.bv_nat 9 0) v_10605));
      v_10608 <- eval (extract v_10607 0 16);
      store v_10600 v_10608 2;
      v_10610 <- eval (eq v_10605 (expression.bv_nat 8 0));
      v_10611 <- eval (notBool_ v_10610);
      v_10614 <- getRegister zf;
      v_10620 <- getRegister sf;
      v_10627 <- getRegister pf;
      v_10631 <- eval (eq v_10605 (expression.bv_nat 8 1));
      v_10635 <- eval (bit_and v_10611 undef);
      v_10636 <- getRegister of;
      v_10642 <- eval (uge v_10605 (expression.bv_nat 8 16));
      v_10647 <- getRegister cf;
      v_10653 <- getRegister af;
      setRegister af (bit_or v_10635 (bit_and v_10610 (eq v_10653 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_10642 undef) (bit_and (notBool_ v_10642) (bit_or (bit_and v_10611 (isBitSet v_10607 16)) (bit_and v_10610 (eq v_10647 (expression.bv_nat 1 1))))));
      setRegister of (bit_or (bit_and v_10631 (isBitSet v_10601 0)) (bit_and (notBool_ v_10631) (bit_or v_10635 (bit_and v_10610 (eq v_10636 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_10611 (parityFlag (extract v_10607 8 16))) (bit_and v_10610 (eq v_10627 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_10611 (isBitSet v_10607 0)) (bit_and v_10610 (eq v_10620 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_10611 (eq v_10608 (expression.bv_nat 16 0))) (bit_and v_10610 (eq v_10614 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3027 : imm int) (v_3026 : Mem) => do
      v_10663 <- evaluateAddress v_3026;
      v_10664 <- load v_10663 2;
      v_10667 <- eval (bv_and (handleImmediateWithSignExtend v_3027 8 8) (expression.bv_nat 8 31));
      v_10669 <- eval (lshr (concat v_10664 (expression.bv_nat 1 0)) (concat (expression.bv_nat 9 0) v_10667));
      v_10670 <- eval (extract v_10669 0 16);
      store v_10663 v_10670 2;
      v_10672 <- eval (eq v_10667 (expression.bv_nat 8 0));
      v_10673 <- eval (notBool_ v_10672);
      v_10676 <- getRegister zf;
      v_10682 <- getRegister sf;
      v_10689 <- getRegister pf;
      v_10693 <- eval (eq v_10667 (expression.bv_nat 8 1));
      v_10697 <- eval (bit_and v_10673 undef);
      v_10698 <- getRegister of;
      v_10704 <- eval (uge v_10667 (expression.bv_nat 8 16));
      v_10709 <- getRegister cf;
      v_10715 <- getRegister af;
      setRegister af (bit_or v_10697 (bit_and v_10672 (eq v_10715 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_10704 undef) (bit_and (notBool_ v_10704) (bit_or (bit_and v_10673 (isBitSet v_10669 16)) (bit_and v_10672 (eq v_10709 (expression.bv_nat 1 1))))));
      setRegister of (bit_or (bit_and v_10693 (isBitSet v_10664 0)) (bit_and (notBool_ v_10693) (bit_or v_10697 (bit_and v_10672 (eq v_10698 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_10673 (parityFlag (extract v_10669 8 16))) (bit_and v_10672 (eq v_10689 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_10673 (isBitSet v_10669 0)) (bit_and v_10672 (eq v_10682 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_10673 (eq v_10670 (expression.bv_nat 16 0))) (bit_and v_10672 (eq v_10676 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3030 : Mem) => do
      v_11146 <- evaluateAddress v_3030;
      v_11147 <- load v_11146 2;
      v_11149 <- eval (lshr (concat v_11147 (expression.bv_nat 1 0)) (expression.bv_nat 17 1));
      v_11150 <- eval (extract v_11149 0 16);
      store v_11146 v_11150 2;
      setRegister af undef;
      setRegister cf (isBitSet v_11149 16);
      setRegister of (isBitSet v_11147 0);
      setRegister pf (parityFlag (extract v_11149 8 16));
      setRegister sf (isBitSet v_11149 0);
      setRegister zf (zeroFlag v_11150);
      pure ()
    pat_end
