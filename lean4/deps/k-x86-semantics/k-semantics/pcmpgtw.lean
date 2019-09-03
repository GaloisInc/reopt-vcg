def pcmpgtw1 : instruction :=
  definst "pcmpgtw" $ do
    pattern fun (v_2433 : reg (bv 128)) (v_2434 : reg (bv 128)) => do
      v_3996 <- getRegister v_2434;
      v_3998 <- getRegister v_2433;
      setRegister (lhs.of_reg v_2434) (concat (mux (sgt (extract v_3996 0 16) (extract v_3998 0 16)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_3996 16 32) (extract v_3998 16 32)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_3996 32 48) (extract v_3998 32 48)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_3996 48 64) (extract v_3998 48 64)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_3996 64 80) (extract v_3998 64 80)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_3996 80 96) (extract v_3998 80 96)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_3996 96 112) (extract v_3998 96 112)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (mux (sgt (extract v_3996 112 128) (extract v_3998 112 128)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_2429 : Mem) (v_2430 : reg (bv 128)) => do
      v_11133 <- getRegister v_2430;
      v_11135 <- evaluateAddress v_2429;
      v_11136 <- load v_11135 16;
      setRegister (lhs.of_reg v_2430) (concat (mux (sgt (extract v_11133 0 16) (extract v_11136 0 16)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_11133 16 32) (extract v_11136 16 32)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_11133 32 48) (extract v_11136 32 48)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_11133 48 64) (extract v_11136 48 64)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_11133 64 80) (extract v_11136 64 80)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_11133 80 96) (extract v_11136 80 96)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_11133 96 112) (extract v_11136 96 112)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (mux (sgt (extract v_11133 112 128) (extract v_11136 112 128)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)))))))));
      pure ()
    pat_end
