def blendvps1 : instruction :=
  definst "blendvps" $ do
    pattern fun xmm0 (v_2959 : reg (bv 128)) (v_2960 : reg (bv 128)) => do
      v_6012 <- getRegister ymm0;
      v_6015 <- getRegister v_2960;
      v_6017 <- getRegister v_2959;
      setRegister (lhs.of_reg v_2960) (concat (mux (eq (extract v_6012 128 129) (expression.bv_nat 1 0)) (extract v_6015 0 32) (extract v_6017 0 32)) (concat (mux (eq (extract v_6012 160 161) (expression.bv_nat 1 0)) (extract v_6015 32 64) (extract v_6017 32 64)) (concat (mux (eq (extract v_6012 192 193) (expression.bv_nat 1 0)) (extract v_6015 64 96) (extract v_6017 64 96)) (mux (eq (extract v_6012 224 225) (expression.bv_nat 1 0)) (extract v_6015 96 128) (extract v_6017 96 128)))));
      pure ()
    pat_end;
    pattern fun xmm0 (v_2954 : Mem) (v_2955 : reg (bv 128)) => do
      v_9851 <- getRegister ymm0;
      v_9854 <- getRegister v_2955;
      v_9856 <- evaluateAddress v_2954;
      v_9857 <- load v_9856 16;
      setRegister (lhs.of_reg v_2955) (concat (mux (eq (extract v_9851 128 129) (expression.bv_nat 1 0)) (extract v_9854 0 32) (extract v_9857 0 32)) (concat (mux (eq (extract v_9851 160 161) (expression.bv_nat 1 0)) (extract v_9854 32 64) (extract v_9857 32 64)) (concat (mux (eq (extract v_9851 192 193) (expression.bv_nat 1 0)) (extract v_9854 64 96) (extract v_9857 64 96)) (mux (eq (extract v_9851 224 225) (expression.bv_nat 1 0)) (extract v_9854 96 128) (extract v_9857 96 128)))));
      pure ()
    pat_end
