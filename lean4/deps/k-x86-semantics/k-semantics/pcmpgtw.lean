def pcmpgtw1 : instruction :=
  definst "pcmpgtw" $ do
    pattern fun (v_2482 : reg (bv 128)) (v_2483 : reg (bv 128)) => do
      v_4047 <- getRegister v_2483;
      v_4049 <- getRegister v_2482;
      setRegister (lhs.of_reg v_2483) (concat (mux (sgt (extract v_4047 0 16) (extract v_4049 0 16)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_4047 16 32) (extract v_4049 16 32)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_4047 32 48) (extract v_4049 32 48)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_4047 48 64) (extract v_4049 48 64)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_4047 64 80) (extract v_4049 64 80)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_4047 80 96) (extract v_4049 80 96)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_4047 96 112) (extract v_4049 96 112)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (mux (sgt (extract v_4047 112 128) (extract v_4049 112 128)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_2479 : Mem) (v_2478 : reg (bv 128)) => do
      v_11010 <- getRegister v_2478;
      v_11012 <- evaluateAddress v_2479;
      v_11013 <- load v_11012 16;
      setRegister (lhs.of_reg v_2478) (concat (mux (sgt (extract v_11010 0 16) (extract v_11013 0 16)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_11010 16 32) (extract v_11013 16 32)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_11010 32 48) (extract v_11013 32 48)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_11010 48 64) (extract v_11013 48 64)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_11010 64 80) (extract v_11013 64 80)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_11010 80 96) (extract v_11013 80 96)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_11010 96 112) (extract v_11013 96 112)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (mux (sgt (extract v_11010 112 128) (extract v_11013 112 128)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)))))))));
      pure ()
    pat_end
