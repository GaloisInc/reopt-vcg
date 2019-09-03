def vblendvps1 : instruction :=
  definst "vblendvps" $ do
    pattern fun (v_2847 : reg (bv 128)) (v_2848 : reg (bv 128)) (v_2849 : reg (bv 128)) (v_2850 : reg (bv 128)) => do
      v_5436 <- getRegister v_2847;
      v_5439 <- getRegister v_2849;
      v_5441 <- getRegister v_2848;
      setRegister (lhs.of_reg v_2850) (concat (mux (eq (extract v_5436 0 1) (expression.bv_nat 1 0)) (extract v_5439 0 32) (extract v_5441 0 32)) (concat (mux (eq (extract v_5436 32 33) (expression.bv_nat 1 0)) (extract v_5439 32 64) (extract v_5441 32 64)) (concat (mux (eq (extract v_5436 64 65) (expression.bv_nat 1 0)) (extract v_5439 64 96) (extract v_5441 64 96)) (mux (eq (extract v_5436 96 97) (expression.bv_nat 1 0)) (extract v_5439 96 128) (extract v_5441 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2858 : reg (bv 256)) (v_2859 : reg (bv 256)) (v_2860 : reg (bv 256)) (v_2861 : reg (bv 256)) => do
      v_5469 <- getRegister v_2858;
      v_5472 <- getRegister v_2860;
      v_5474 <- getRegister v_2859;
      setRegister (lhs.of_reg v_2861) (concat (mux (eq (extract v_5469 0 1) (expression.bv_nat 1 0)) (extract v_5472 0 32) (extract v_5474 0 32)) (concat (mux (eq (extract v_5469 32 33) (expression.bv_nat 1 0)) (extract v_5472 32 64) (extract v_5474 32 64)) (concat (mux (eq (extract v_5469 64 65) (expression.bv_nat 1 0)) (extract v_5472 64 96) (extract v_5474 64 96)) (concat (mux (eq (extract v_5469 96 97) (expression.bv_nat 1 0)) (extract v_5472 96 128) (extract v_5474 96 128)) (concat (mux (eq (extract v_5469 128 129) (expression.bv_nat 1 0)) (extract v_5472 128 160) (extract v_5474 128 160)) (concat (mux (eq (extract v_5469 160 161) (expression.bv_nat 1 0)) (extract v_5472 160 192) (extract v_5474 160 192)) (concat (mux (eq (extract v_5469 192 193) (expression.bv_nat 1 0)) (extract v_5472 192 224) (extract v_5474 192 224)) (mux (eq (extract v_5469 224 225) (expression.bv_nat 1 0)) (extract v_5472 224 256) (extract v_5474 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_2841 : reg (bv 128)) (v_2838 : Mem) (v_2842 : reg (bv 128)) (v_2843 : reg (bv 128)) => do
      v_9800 <- getRegister v_2841;
      v_9803 <- getRegister v_2842;
      v_9805 <- evaluateAddress v_2838;
      v_9806 <- load v_9805 16;
      setRegister (lhs.of_reg v_2843) (concat (mux (eq (extract v_9800 0 1) (expression.bv_nat 1 0)) (extract v_9803 0 32) (extract v_9806 0 32)) (concat (mux (eq (extract v_9800 32 33) (expression.bv_nat 1 0)) (extract v_9803 32 64) (extract v_9806 32 64)) (concat (mux (eq (extract v_9800 64 65) (expression.bv_nat 1 0)) (extract v_9803 64 96) (extract v_9806 64 96)) (mux (eq (extract v_9800 96 97) (expression.bv_nat 1 0)) (extract v_9803 96 128) (extract v_9806 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2852 : reg (bv 256)) (v_2851 : Mem) (v_2853 : reg (bv 256)) (v_2854 : reg (bv 256)) => do
      v_9828 <- getRegister v_2852;
      v_9831 <- getRegister v_2853;
      v_9833 <- evaluateAddress v_2851;
      v_9834 <- load v_9833 32;
      setRegister (lhs.of_reg v_2854) (concat (mux (eq (extract v_9828 0 1) (expression.bv_nat 1 0)) (extract v_9831 0 32) (extract v_9834 0 32)) (concat (mux (eq (extract v_9828 32 33) (expression.bv_nat 1 0)) (extract v_9831 32 64) (extract v_9834 32 64)) (concat (mux (eq (extract v_9828 64 65) (expression.bv_nat 1 0)) (extract v_9831 64 96) (extract v_9834 64 96)) (concat (mux (eq (extract v_9828 96 97) (expression.bv_nat 1 0)) (extract v_9831 96 128) (extract v_9834 96 128)) (concat (mux (eq (extract v_9828 128 129) (expression.bv_nat 1 0)) (extract v_9831 128 160) (extract v_9834 128 160)) (concat (mux (eq (extract v_9828 160 161) (expression.bv_nat 1 0)) (extract v_9831 160 192) (extract v_9834 160 192)) (concat (mux (eq (extract v_9828 192 193) (expression.bv_nat 1 0)) (extract v_9831 192 224) (extract v_9834 192 224)) (mux (eq (extract v_9828 224 225) (expression.bv_nat 1 0)) (extract v_9831 224 256) (extract v_9834 224 256)))))))));
      pure ()
    pat_end
