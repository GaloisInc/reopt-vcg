def blendvpd1 : instruction :=
  definst "blendvpd" $ do
    pattern fun xmm0 (v_2937 : reg (bv 128)) (v_2938 : reg (bv 128)) => do
      v_5834 <- getRegister ymm0;
      v_5837 <- getRegister v_2938;
      v_5839 <- getRegister v_2937;
      setRegister (lhs.of_reg v_2938) (concat (mux (eq (extract v_5834 128 129) (expression.bv_nat 1 0)) (extract v_5837 0 64) (extract v_5839 0 64)) (mux (eq (extract v_5834 192 193) (expression.bv_nat 1 0)) (extract v_5837 64 128) (extract v_5839 64 128)));
      pure ()
    pat_end;
    pattern fun xmm0 (v_2932 : Mem) (v_2933 : reg (bv 128)) => do
      v_9543 <- getRegister ymm0;
      v_9546 <- getRegister v_2933;
      v_9548 <- evaluateAddress v_2932;
      v_9549 <- load v_9548 16;
      setRegister (lhs.of_reg v_2933) (concat (mux (eq (extract v_9543 128 129) (expression.bv_nat 1 0)) (extract v_9546 0 64) (extract v_9549 0 64)) (mux (eq (extract v_9543 192 193) (expression.bv_nat 1 0)) (extract v_9546 64 128) (extract v_9549 64 128)));
      pure ()
    pat_end
