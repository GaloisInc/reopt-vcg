def vblendvpd1 : instruction :=
  definst "vblendvpd" $ do
    pattern fun (v_2821 : reg (bv 128)) (v_2822 : reg (bv 128)) (v_2823 : reg (bv 128)) (v_2824 : reg (bv 128)) => do
      v_5382 <- getRegister v_2821;
      v_5385 <- getRegister v_2823;
      v_5387 <- getRegister v_2822;
      setRegister (lhs.of_reg v_2824) (concat (mux (eq (extract v_5382 0 1) (expression.bv_nat 1 0)) (extract v_5385 0 64) (extract v_5387 0 64)) (mux (eq (extract v_5382 64 65) (expression.bv_nat 1 0)) (extract v_5385 64 128) (extract v_5387 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2832 : reg (bv 256)) (v_2833 : reg (bv 256)) (v_2834 : reg (bv 256)) (v_2835 : reg (bv 256)) => do
      v_5403 <- getRegister v_2832;
      v_5406 <- getRegister v_2834;
      v_5408 <- getRegister v_2833;
      setRegister (lhs.of_reg v_2835) (concat (mux (eq (extract v_5403 0 1) (expression.bv_nat 1 0)) (extract v_5406 0 64) (extract v_5408 0 64)) (concat (mux (eq (extract v_5403 64 65) (expression.bv_nat 1 0)) (extract v_5406 64 128) (extract v_5408 64 128)) (concat (mux (eq (extract v_5403 128 129) (expression.bv_nat 1 0)) (extract v_5406 128 192) (extract v_5408 128 192)) (mux (eq (extract v_5403 192 193) (expression.bv_nat 1 0)) (extract v_5406 192 256) (extract v_5408 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2815 : reg (bv 128)) (v_2812 : Mem) (v_2816 : reg (bv 128)) (v_2817 : reg (bv 128)) => do
      v_9756 <- getRegister v_2815;
      v_9759 <- getRegister v_2816;
      v_9761 <- evaluateAddress v_2812;
      v_9762 <- load v_9761 16;
      setRegister (lhs.of_reg v_2817) (concat (mux (eq (extract v_9756 0 1) (expression.bv_nat 1 0)) (extract v_9759 0 64) (extract v_9762 0 64)) (mux (eq (extract v_9756 64 65) (expression.bv_nat 1 0)) (extract v_9759 64 128) (extract v_9762 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2826 : reg (bv 256)) (v_2825 : Mem) (v_2827 : reg (bv 256)) (v_2828 : reg (bv 256)) => do
      v_9772 <- getRegister v_2826;
      v_9775 <- getRegister v_2827;
      v_9777 <- evaluateAddress v_2825;
      v_9778 <- load v_9777 32;
      setRegister (lhs.of_reg v_2828) (concat (mux (eq (extract v_9772 0 1) (expression.bv_nat 1 0)) (extract v_9775 0 64) (extract v_9778 0 64)) (concat (mux (eq (extract v_9772 64 65) (expression.bv_nat 1 0)) (extract v_9775 64 128) (extract v_9778 64 128)) (concat (mux (eq (extract v_9772 128 129) (expression.bv_nat 1 0)) (extract v_9775 128 192) (extract v_9778 128 192)) (mux (eq (extract v_9772 192 193) (expression.bv_nat 1 0)) (extract v_9775 192 256) (extract v_9778 192 256)))));
      pure ()
    pat_end
