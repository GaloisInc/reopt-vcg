def vblendpd1 : instruction :=
  definst "vblendpd" $ do
    pattern fun (v_2779 : imm int) (v_2783 : reg (bv 128)) (v_2784 : reg (bv 128)) (v_2785 : reg (bv 128)) => do
      v_5697 <- eval (handleImmediateWithSignExtend v_2779 8 8);
      v_5700 <- getRegister v_2784;
      v_5702 <- getRegister v_2783;
      setRegister (lhs.of_reg v_2785) (concat (mux (eq (extract v_5697 6 7) (expression.bv_nat 1 0)) (extract v_5700 0 64) (extract v_5702 0 64)) (mux (eq (extract v_5697 7 8) (expression.bv_nat 1 0)) (extract v_5700 64 128) (extract v_5702 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2792 : imm int) (v_2793 : reg (bv 256)) (v_2794 : reg (bv 256)) (v_2795 : reg (bv 256)) => do
      v_5718 <- eval (handleImmediateWithSignExtend v_2792 8 8);
      v_5721 <- getRegister v_2794;
      v_5723 <- getRegister v_2793;
      setRegister (lhs.of_reg v_2795) (concat (mux (eq (extract v_5718 4 5) (expression.bv_nat 1 0)) (extract v_5721 0 64) (extract v_5723 0 64)) (concat (mux (eq (extract v_5718 5 6) (expression.bv_nat 1 0)) (extract v_5721 64 128) (extract v_5723 64 128)) (concat (mux (eq (extract v_5718 6 7) (expression.bv_nat 1 0)) (extract v_5721 128 192) (extract v_5723 128 192)) (mux (eq (extract v_5718 7 8) (expression.bv_nat 1 0)) (extract v_5721 192 256) (extract v_5723 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2774 : imm int) (v_2773 : Mem) (v_2777 : reg (bv 128)) (v_2778 : reg (bv 128)) => do
      v_11174 <- eval (handleImmediateWithSignExtend v_2774 8 8);
      v_11177 <- getRegister v_2777;
      v_11179 <- evaluateAddress v_2773;
      v_11180 <- load v_11179 16;
      setRegister (lhs.of_reg v_2778) (concat (mux (eq (extract v_11174 6 7) (expression.bv_nat 1 0)) (extract v_11177 0 64) (extract v_11180 0 64)) (mux (eq (extract v_11174 7 8) (expression.bv_nat 1 0)) (extract v_11177 64 128) (extract v_11180 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2787 : imm int) (v_2786 : Mem) (v_2788 : reg (bv 256)) (v_2789 : reg (bv 256)) => do
      v_11190 <- eval (handleImmediateWithSignExtend v_2787 8 8);
      v_11193 <- getRegister v_2788;
      v_11195 <- evaluateAddress v_2786;
      v_11196 <- load v_11195 32;
      setRegister (lhs.of_reg v_2789) (concat (mux (eq (extract v_11190 4 5) (expression.bv_nat 1 0)) (extract v_11193 0 64) (extract v_11196 0 64)) (concat (mux (eq (extract v_11190 5 6) (expression.bv_nat 1 0)) (extract v_11193 64 128) (extract v_11196 64 128)) (concat (mux (eq (extract v_11190 6 7) (expression.bv_nat 1 0)) (extract v_11193 128 192) (extract v_11196 128 192)) (mux (eq (extract v_11190 7 8) (expression.bv_nat 1 0)) (extract v_11193 192 256) (extract v_11196 192 256)))));
      pure ()
    pat_end
