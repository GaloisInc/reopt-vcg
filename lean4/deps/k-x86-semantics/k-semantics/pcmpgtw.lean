def pcmpgtw1 : instruction :=
  definst "pcmpgtw" $ do
    pattern fun (v_2419 : reg (bv 128)) (v_2420 : reg (bv 128)) => do
      v_3983 <- getRegister v_2420;
      v_3985 <- getRegister v_2419;
      setRegister (lhs.of_reg v_2420) (concat (mux (sgt (extract v_3983 0 16) (extract v_3985 0 16)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_3983 16 32) (extract v_3985 16 32)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_3983 32 48) (extract v_3985 32 48)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_3983 48 64) (extract v_3985 48 64)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_3983 64 80) (extract v_3985 64 80)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_3983 80 96) (extract v_3985 80 96)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_3983 96 112) (extract v_3985 96 112)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (mux (sgt (extract v_3983 112 128) (extract v_3985 112 128)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_2414 : Mem) (v_2415 : reg (bv 128)) => do
      v_11450 <- getRegister v_2415;
      v_11452 <- evaluateAddress v_2414;
      v_11453 <- load v_11452 16;
      setRegister (lhs.of_reg v_2415) (concat (mux (sgt (extract v_11450 0 16) (extract v_11453 0 16)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_11450 16 32) (extract v_11453 16 32)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_11450 32 48) (extract v_11453 32 48)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_11450 48 64) (extract v_11453 48 64)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_11450 64 80) (extract v_11453 64 80)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_11450 80 96) (extract v_11453 80 96)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_11450 96 112) (extract v_11453 96 112)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (mux (sgt (extract v_11450 112 128) (extract v_11453 112 128)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)))))))));
      pure ()
    pat_end
