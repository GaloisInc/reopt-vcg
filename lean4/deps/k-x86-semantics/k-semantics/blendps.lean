def blendps1 : instruction :=
  definst "blendps" $ do
    pattern fun (v_2925 : imm int) (v_2928 : reg (bv 128)) (v_2929 : reg (bv 128)) => do
      v_5803 <- eval (handleImmediateWithSignExtend v_2925 8 8);
      v_5806 <- getRegister v_2929;
      v_5808 <- getRegister v_2928;
      setRegister (lhs.of_reg v_2929) (concat (mux (eq (extract v_5803 4 5) (expression.bv_nat 1 0)) (extract v_5806 0 32) (extract v_5808 0 32)) (concat (mux (eq (extract v_5803 5 6) (expression.bv_nat 1 0)) (extract v_5806 32 64) (extract v_5808 32 64)) (concat (mux (eq (extract v_5803 6 7) (expression.bv_nat 1 0)) (extract v_5806 64 96) (extract v_5808 64 96)) (mux (eq (extract v_5803 7 8) (expression.bv_nat 1 0)) (extract v_5806 96 128) (extract v_5808 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2920 : imm int) (v_2922 : Mem) (v_2923 : reg (bv 128)) => do
      v_9515 <- eval (handleImmediateWithSignExtend v_2920 8 8);
      v_9518 <- getRegister v_2923;
      v_9520 <- evaluateAddress v_2922;
      v_9521 <- load v_9520 16;
      setRegister (lhs.of_reg v_2923) (concat (mux (eq (extract v_9515 4 5) (expression.bv_nat 1 0)) (extract v_9518 0 32) (extract v_9521 0 32)) (concat (mux (eq (extract v_9515 5 6) (expression.bv_nat 1 0)) (extract v_9518 32 64) (extract v_9521 32 64)) (concat (mux (eq (extract v_9515 6 7) (expression.bv_nat 1 0)) (extract v_9518 64 96) (extract v_9521 64 96)) (mux (eq (extract v_9515 7 8) (expression.bv_nat 1 0)) (extract v_9518 96 128) (extract v_9521 96 128)))));
      pure ()
    pat_end
