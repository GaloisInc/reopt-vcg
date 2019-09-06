def pcmpeqw1 : instruction :=
  definst "pcmpeqw" $ do
    pattern fun (v_2474 : reg (bv 128)) (v_2475 : reg (bv 128)) => do
      v_3900 <- getRegister v_2475;
      v_3902 <- getRegister v_2474;
      setRegister (lhs.of_reg v_2475) (concat (mux (eq (extract v_3900 0 16) (extract v_3902 0 16)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_3900 16 32) (extract v_3902 16 32)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_3900 32 48) (extract v_3902 32 48)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_3900 48 64) (extract v_3902 48 64)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_3900 64 80) (extract v_3902 64 80)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_3900 80 96) (extract v_3902 80 96)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_3900 96 112) (extract v_3902 96 112)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (mux (eq (extract v_3900 112 128) (extract v_3902 112 128)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_2470 : Mem) (v_2471 : reg (bv 128)) => do
      v_10824 <- getRegister v_2471;
      v_10826 <- evaluateAddress v_2470;
      v_10827 <- load v_10826 16;
      setRegister (lhs.of_reg v_2471) (concat (mux (eq (extract v_10824 0 16) (extract v_10827 0 16)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_10824 16 32) (extract v_10827 16 32)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_10824 32 48) (extract v_10827 32 48)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_10824 48 64) (extract v_10827 48 64)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_10824 64 80) (extract v_10827 64 80)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_10824 80 96) (extract v_10827 80 96)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_10824 96 112) (extract v_10827 96 112)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (mux (eq (extract v_10824 112 128) (extract v_10827 112 128)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)))))))));
      pure ()
    pat_end
