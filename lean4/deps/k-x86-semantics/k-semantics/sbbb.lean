def sbbb1 : instruction :=
  definst "sbbb" $ do
    pattern fun (v_3296 : imm int) (v_3300 : reg (bv 8)) => do
      v_6555 <- getRegister cf;
      v_6556 <- eval (handleImmediateWithSignExtend v_3296 8 8);
      v_6558 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_6556 (expression.bv_nat 8 255)));
      v_6561 <- getRegister v_3300;
      v_6563 <- eval (add (mux v_6555 v_6558 (add v_6558 (expression.bv_nat 9 1))) (concat (expression.bv_nat 1 0) v_6561));
      v_6564 <- eval (extract v_6563 1 9);
      v_6566 <- eval (isBitSet v_6563 1);
      v_6570 <- eval (eq (bv_xor (extract v_6556 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3300) v_6564;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_6556 v_6561) 3) (isBitSet v_6563 4)));
      setRegister cf (isBitClear v_6563 0);
      setRegister of (bit_and (eq v_6570 (isBitSet v_6561 0)) (notBool_ (eq v_6570 v_6566)));
      setRegister pf (parityFlag v_6564);
      setRegister sf v_6566;
      setRegister zf (zeroFlag v_6564);
      pure ()
    pat_end;
    pattern fun (v_3313 : reg (bv 8)) (v_3314 : reg (bv 8)) => do
      v_6627 <- getRegister cf;
      v_6628 <- getRegister v_3313;
      v_6630 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_6628 (expression.bv_nat 8 255)));
      v_6633 <- getRegister v_3314;
      v_6635 <- eval (add (mux v_6627 v_6630 (add v_6630 (expression.bv_nat 9 1))) (concat (expression.bv_nat 1 0) v_6633));
      v_6636 <- eval (extract v_6635 1 9);
      v_6638 <- eval (isBitSet v_6635 1);
      v_6642 <- eval (eq (bv_xor (extract v_6628 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3314) v_6636;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_6628 v_6633) 3) (isBitSet v_6635 4)));
      setRegister cf (isBitClear v_6635 0);
      setRegister of (bit_and (eq v_6642 (isBitSet v_6633 0)) (notBool_ (eq v_6642 v_6638)));
      setRegister pf (parityFlag v_6636);
      setRegister sf v_6638;
      setRegister zf (zeroFlag v_6636);
      pure ()
    pat_end;
    pattern fun (v_3301 : Mem) (v_3304 : reg (bv 8)) => do
      v_10723 <- getRegister cf;
      v_10724 <- evaluateAddress v_3301;
      v_10725 <- load v_10724 1;
      v_10727 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_10725 (expression.bv_nat 8 255)));
      v_10730 <- getRegister v_3304;
      v_10732 <- eval (add (mux v_10723 v_10727 (add v_10727 (expression.bv_nat 9 1))) (concat (expression.bv_nat 1 0) v_10730));
      v_10733 <- eval (extract v_10732 1 9);
      v_10735 <- eval (isBitSet v_10732 1);
      v_10739 <- eval (eq (bv_xor (extract v_10725 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3304) v_10733;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10725 v_10730) 3) (isBitSet v_10732 4)));
      setRegister cf (isBitClear v_10732 0);
      setRegister of (bit_and (eq v_10739 (isBitSet v_10730 0)) (notBool_ (eq v_10739 v_10735)));
      setRegister pf (parityFlag v_10733);
      setRegister sf v_10735;
      setRegister zf (zeroFlag v_10733);
      pure ()
    pat_end;
    pattern fun (v_3265 : imm int) (v_3266 : Mem) => do
      v_12781 <- evaluateAddress v_3266;
      v_12782 <- getRegister cf;
      v_12783 <- eval (handleImmediateWithSignExtend v_3265 8 8);
      v_12785 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_12783 (expression.bv_nat 8 255)));
      v_12788 <- load v_12781 1;
      v_12790 <- eval (add (mux v_12782 v_12785 (add v_12785 (expression.bv_nat 9 1))) (concat (expression.bv_nat 1 0) v_12788));
      v_12791 <- eval (extract v_12790 1 9);
      store v_12781 v_12791 1;
      v_12794 <- eval (isBitSet v_12790 1);
      v_12798 <- eval (eq (bv_xor (extract v_12783 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_12783 v_12788) 3) (isBitSet v_12790 4)));
      setRegister cf (isBitClear v_12790 0);
      setRegister of (bit_and (eq v_12798 (isBitSet v_12788 0)) (notBool_ (eq v_12798 v_12794)));
      setRegister pf (parityFlag v_12791);
      setRegister sf v_12794;
      setRegister zf (zeroFlag v_12791);
      pure ()
    pat_end;
    pattern fun (v_3276 : reg (bv 8)) (v_3273 : Mem) => do
      v_12851 <- evaluateAddress v_3273;
      v_12852 <- getRegister cf;
      v_12853 <- getRegister v_3276;
      v_12855 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_12853 (expression.bv_nat 8 255)));
      v_12858 <- load v_12851 1;
      v_12860 <- eval (add (mux v_12852 v_12855 (add v_12855 (expression.bv_nat 9 1))) (concat (expression.bv_nat 1 0) v_12858));
      v_12861 <- eval (extract v_12860 1 9);
      store v_12851 v_12861 1;
      v_12864 <- eval (isBitSet v_12860 1);
      v_12868 <- eval (eq (bv_xor (extract v_12853 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_12853 v_12858) 3) (isBitSet v_12860 4)));
      setRegister cf (isBitClear v_12860 0);
      setRegister of (bit_and (eq v_12868 (isBitSet v_12858 0)) (notBool_ (eq v_12868 v_12864)));
      setRegister pf (parityFlag v_12861);
      setRegister sf v_12864;
      setRegister zf (zeroFlag v_12861);
      pure ()
    pat_end
