def blendvps1 : instruction :=
  definst "blendvps" $ do
    pattern fun xmm0 (v_2946 : reg (bv 128)) (v_2947 : reg (bv 128)) => do
      v_5853 <- getRegister ymm0;
      v_5856 <- getRegister v_2947;
      v_5858 <- getRegister v_2946;
      setRegister (lhs.of_reg v_2947) (concat (mux (eq (extract v_5853 128 129) (expression.bv_nat 1 0)) (extract v_5856 0 32) (extract v_5858 0 32)) (concat (mux (eq (extract v_5853 160 161) (expression.bv_nat 1 0)) (extract v_5856 32 64) (extract v_5858 32 64)) (concat (mux (eq (extract v_5853 192 193) (expression.bv_nat 1 0)) (extract v_5856 64 96) (extract v_5858 64 96)) (mux (eq (extract v_5853 224 225) (expression.bv_nat 1 0)) (extract v_5856 96 128) (extract v_5858 96 128)))));
      pure ()
    pat_end;
    pattern fun xmm0 (v_2941 : Mem) (v_2942 : reg (bv 128)) => do
      v_9559 <- getRegister ymm0;
      v_9562 <- getRegister v_2942;
      v_9564 <- evaluateAddress v_2941;
      v_9565 <- load v_9564 16;
      setRegister (lhs.of_reg v_2942) (concat (mux (eq (extract v_9559 128 129) (expression.bv_nat 1 0)) (extract v_9562 0 32) (extract v_9565 0 32)) (concat (mux (eq (extract v_9559 160 161) (expression.bv_nat 1 0)) (extract v_9562 32 64) (extract v_9565 32 64)) (concat (mux (eq (extract v_9559 192 193) (expression.bv_nat 1 0)) (extract v_9562 64 96) (extract v_9565 64 96)) (mux (eq (extract v_9559 224 225) (expression.bv_nat 1 0)) (extract v_9562 96 128) (extract v_9565 96 128)))));
      pure ()
    pat_end
