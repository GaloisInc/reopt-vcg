def vblendpd1 : instruction :=
  definst "vblendpd" $ do
    pattern fun (v_2766 : imm int) (v_2770 : reg (bv 128)) (v_2771 : reg (bv 128)) (v_2772 : reg (bv 128)) => do
      v_5238 <- eval (handleImmediateWithSignExtend v_2766 8 8);
      v_5241 <- getRegister v_2771;
      v_5243 <- getRegister v_2770;
      setRegister (lhs.of_reg v_2772) (concat (mux (eq (extract v_5238 6 7) (expression.bv_nat 1 0)) (extract v_5241 0 64) (extract v_5243 0 64)) (mux (eq (extract v_5238 7 8) (expression.bv_nat 1 0)) (extract v_5241 64 128) (extract v_5243 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2779 : imm int) (v_2781 : reg (bv 256)) (v_2782 : reg (bv 256)) (v_2783 : reg (bv 256)) => do
      v_5259 <- eval (handleImmediateWithSignExtend v_2779 8 8);
      v_5262 <- getRegister v_2782;
      v_5264 <- getRegister v_2781;
      setRegister (lhs.of_reg v_2783) (concat (mux (eq (extract v_5259 4 5) (expression.bv_nat 1 0)) (extract v_5262 0 64) (extract v_5264 0 64)) (concat (mux (eq (extract v_5259 5 6) (expression.bv_nat 1 0)) (extract v_5262 64 128) (extract v_5264 64 128)) (concat (mux (eq (extract v_5259 6 7) (expression.bv_nat 1 0)) (extract v_5262 128 192) (extract v_5264 128 192)) (mux (eq (extract v_5259 7 8) (expression.bv_nat 1 0)) (extract v_5262 192 256) (extract v_5264 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2761 : imm int) (v_2760 : Mem) (v_2764 : reg (bv 128)) (v_2765 : reg (bv 128)) => do
      v_9632 <- eval (handleImmediateWithSignExtend v_2761 8 8);
      v_9635 <- getRegister v_2764;
      v_9637 <- evaluateAddress v_2760;
      v_9638 <- load v_9637 16;
      setRegister (lhs.of_reg v_2765) (concat (mux (eq (extract v_9632 6 7) (expression.bv_nat 1 0)) (extract v_9635 0 64) (extract v_9638 0 64)) (mux (eq (extract v_9632 7 8) (expression.bv_nat 1 0)) (extract v_9635 64 128) (extract v_9638 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2774 : imm int) (v_2773 : Mem) (v_2775 : reg (bv 256)) (v_2776 : reg (bv 256)) => do
      v_9648 <- eval (handleImmediateWithSignExtend v_2774 8 8);
      v_9651 <- getRegister v_2775;
      v_9653 <- evaluateAddress v_2773;
      v_9654 <- load v_9653 32;
      setRegister (lhs.of_reg v_2776) (concat (mux (eq (extract v_9648 4 5) (expression.bv_nat 1 0)) (extract v_9651 0 64) (extract v_9654 0 64)) (concat (mux (eq (extract v_9648 5 6) (expression.bv_nat 1 0)) (extract v_9651 64 128) (extract v_9654 64 128)) (concat (mux (eq (extract v_9648 6 7) (expression.bv_nat 1 0)) (extract v_9651 128 192) (extract v_9654 128 192)) (mux (eq (extract v_9648 7 8) (expression.bv_nat 1 0)) (extract v_9651 192 256) (extract v_9654 192 256)))));
      pure ()
    pat_end
