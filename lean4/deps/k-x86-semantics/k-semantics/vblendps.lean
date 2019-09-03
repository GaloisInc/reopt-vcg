def vblendps1 : instruction :=
  definst "vblendps" $ do
    pattern fun (v_2792 : imm int) (v_2796 : reg (bv 128)) (v_2797 : reg (bv 128)) (v_2798 : reg (bv 128)) => do
      v_5292 <- eval (handleImmediateWithSignExtend v_2792 8 8);
      v_5295 <- getRegister v_2797;
      v_5297 <- getRegister v_2796;
      setRegister (lhs.of_reg v_2798) (concat (mux (eq (extract v_5292 4 5) (expression.bv_nat 1 0)) (extract v_5295 0 32) (extract v_5297 0 32)) (concat (mux (eq (extract v_5292 5 6) (expression.bv_nat 1 0)) (extract v_5295 32 64) (extract v_5297 32 64)) (concat (mux (eq (extract v_5292 6 7) (expression.bv_nat 1 0)) (extract v_5295 64 96) (extract v_5297 64 96)) (mux (eq (extract v_5292 7 8) (expression.bv_nat 1 0)) (extract v_5295 96 128) (extract v_5297 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2805 : imm int) (v_2807 : reg (bv 256)) (v_2808 : reg (bv 256)) (v_2809 : reg (bv 256)) => do
      v_5325 <- eval (handleImmediateWithSignExtend v_2805 8 8);
      v_5328 <- getRegister v_2808;
      v_5330 <- getRegister v_2807;
      setRegister (lhs.of_reg v_2809) (concat (mux (eq (extract v_5325 0 1) (expression.bv_nat 1 0)) (extract v_5328 0 32) (extract v_5330 0 32)) (concat (mux (eq (extract v_5325 1 2) (expression.bv_nat 1 0)) (extract v_5328 32 64) (extract v_5330 32 64)) (concat (mux (eq (extract v_5325 2 3) (expression.bv_nat 1 0)) (extract v_5328 64 96) (extract v_5330 64 96)) (concat (mux (eq (extract v_5325 3 4) (expression.bv_nat 1 0)) (extract v_5328 96 128) (extract v_5330 96 128)) (concat (mux (eq (extract v_5325 4 5) (expression.bv_nat 1 0)) (extract v_5328 128 160) (extract v_5330 128 160)) (concat (mux (eq (extract v_5325 5 6) (expression.bv_nat 1 0)) (extract v_5328 160 192) (extract v_5330 160 192)) (concat (mux (eq (extract v_5325 6 7) (expression.bv_nat 1 0)) (extract v_5328 192 224) (extract v_5330 192 224)) (mux (eq (extract v_5325 7 8) (expression.bv_nat 1 0)) (extract v_5328 224 256) (extract v_5330 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_2787 : imm int) (v_2786 : Mem) (v_2790 : reg (bv 128)) (v_2791 : reg (bv 128)) => do
      v_9676 <- eval (handleImmediateWithSignExtend v_2787 8 8);
      v_9679 <- getRegister v_2790;
      v_9681 <- evaluateAddress v_2786;
      v_9682 <- load v_9681 16;
      setRegister (lhs.of_reg v_2791) (concat (mux (eq (extract v_9676 4 5) (expression.bv_nat 1 0)) (extract v_9679 0 32) (extract v_9682 0 32)) (concat (mux (eq (extract v_9676 5 6) (expression.bv_nat 1 0)) (extract v_9679 32 64) (extract v_9682 32 64)) (concat (mux (eq (extract v_9676 6 7) (expression.bv_nat 1 0)) (extract v_9679 64 96) (extract v_9682 64 96)) (mux (eq (extract v_9676 7 8) (expression.bv_nat 1 0)) (extract v_9679 96 128) (extract v_9682 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2800 : imm int) (v_2799 : Mem) (v_2801 : reg (bv 256)) (v_2802 : reg (bv 256)) => do
      v_9704 <- eval (handleImmediateWithSignExtend v_2800 8 8);
      v_9707 <- getRegister v_2801;
      v_9709 <- evaluateAddress v_2799;
      v_9710 <- load v_9709 32;
      setRegister (lhs.of_reg v_2802) (concat (mux (eq (extract v_9704 0 1) (expression.bv_nat 1 0)) (extract v_9707 0 32) (extract v_9710 0 32)) (concat (mux (eq (extract v_9704 1 2) (expression.bv_nat 1 0)) (extract v_9707 32 64) (extract v_9710 32 64)) (concat (mux (eq (extract v_9704 2 3) (expression.bv_nat 1 0)) (extract v_9707 64 96) (extract v_9710 64 96)) (concat (mux (eq (extract v_9704 3 4) (expression.bv_nat 1 0)) (extract v_9707 96 128) (extract v_9710 96 128)) (concat (mux (eq (extract v_9704 4 5) (expression.bv_nat 1 0)) (extract v_9707 128 160) (extract v_9710 128 160)) (concat (mux (eq (extract v_9704 5 6) (expression.bv_nat 1 0)) (extract v_9707 160 192) (extract v_9710 160 192)) (concat (mux (eq (extract v_9704 6 7) (expression.bv_nat 1 0)) (extract v_9707 192 224) (extract v_9710 192 224)) (mux (eq (extract v_9704 7 8) (expression.bv_nat 1 0)) (extract v_9707 224 256) (extract v_9710 224 256)))))))));
      pure ()
    pat_end
