def pcmpeqw1 : instruction :=
  definst "pcmpeqw" $ do
    pattern fun (v_2397 : reg (bv 128)) (v_2398 : reg (bv 128)) => do
      v_3822 <- getRegister v_2398;
      v_3824 <- getRegister v_2397;
      setRegister (lhs.of_reg v_2398) (concat (mux (eq (extract v_3822 0 16) (extract v_3824 0 16)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_3822 16 32) (extract v_3824 16 32)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_3822 32 48) (extract v_3824 32 48)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_3822 48 64) (extract v_3824 48 64)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_3822 64 80) (extract v_3824 64 80)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_3822 80 96) (extract v_3824 80 96)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_3822 96 112) (extract v_3824 96 112)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (mux (eq (extract v_3822 112 128) (extract v_3824 112 128)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_2393 : Mem) (v_2394 : reg (bv 128)) => do
      v_10971 <- getRegister v_2394;
      v_10973 <- evaluateAddress v_2393;
      v_10974 <- load v_10973 16;
      setRegister (lhs.of_reg v_2394) (concat (mux (eq (extract v_10971 0 16) (extract v_10974 0 16)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_10971 16 32) (extract v_10974 16 32)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_10971 32 48) (extract v_10974 32 48)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_10971 48 64) (extract v_10974 48 64)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_10971 64 80) (extract v_10974 64 80)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_10971 80 96) (extract v_10974 80 96)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_10971 96 112) (extract v_10974 96 112)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (mux (eq (extract v_10971 112 128) (extract v_10974 112 128)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)))))))));
      pure ()
    pat_end
