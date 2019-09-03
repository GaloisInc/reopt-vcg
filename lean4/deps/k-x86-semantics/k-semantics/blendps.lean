def blendps1 : instruction :=
  definst "blendps" $ do
    pattern fun (v_2939 : imm int) (v_2941 : reg (bv 128)) (v_2942 : reg (bv 128)) => do
      v_5962 <- eval (handleImmediateWithSignExtend v_2939 8 8);
      v_5965 <- getRegister v_2942;
      v_5967 <- getRegister v_2941;
      setRegister (lhs.of_reg v_2942) (concat (mux (eq (extract v_5962 4 5) (expression.bv_nat 1 0)) (extract v_5965 0 32) (extract v_5967 0 32)) (concat (mux (eq (extract v_5962 5 6) (expression.bv_nat 1 0)) (extract v_5965 32 64) (extract v_5967 32 64)) (concat (mux (eq (extract v_5962 6 7) (expression.bv_nat 1 0)) (extract v_5965 64 96) (extract v_5967 64 96)) (mux (eq (extract v_5962 7 8) (expression.bv_nat 1 0)) (extract v_5965 96 128) (extract v_5967 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2935 : imm int) (v_2934 : Mem) (v_2936 : reg (bv 128)) => do
      v_9807 <- eval (handleImmediateWithSignExtend v_2935 8 8);
      v_9810 <- getRegister v_2936;
      v_9812 <- evaluateAddress v_2934;
      v_9813 <- load v_9812 16;
      setRegister (lhs.of_reg v_2936) (concat (mux (eq (extract v_9807 4 5) (expression.bv_nat 1 0)) (extract v_9810 0 32) (extract v_9813 0 32)) (concat (mux (eq (extract v_9807 5 6) (expression.bv_nat 1 0)) (extract v_9810 32 64) (extract v_9813 32 64)) (concat (mux (eq (extract v_9807 6 7) (expression.bv_nat 1 0)) (extract v_9810 64 96) (extract v_9813 64 96)) (mux (eq (extract v_9807 7 8) (expression.bv_nat 1 0)) (extract v_9810 96 128) (extract v_9813 96 128)))));
      pure ()
    pat_end
