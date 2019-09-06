def pcmpgtw1 : instruction :=
  definst "pcmpgtw" $ do
    pattern fun (v_2510 : reg (bv 128)) (v_2511 : reg (bv 128)) => do
      v_4074 <- getRegister v_2511;
      v_4076 <- getRegister v_2510;
      setRegister (lhs.of_reg v_2511) (concat (mux (sgt (extract v_4074 0 16) (extract v_4076 0 16)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_4074 16 32) (extract v_4076 16 32)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_4074 32 48) (extract v_4076 32 48)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_4074 48 64) (extract v_4076 48 64)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_4074 64 80) (extract v_4076 64 80)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_4074 80 96) (extract v_4076 80 96)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_4074 96 112) (extract v_4076 96 112)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (mux (sgt (extract v_4074 112 128) (extract v_4076 112 128)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_2506 : Mem) (v_2507 : reg (bv 128)) => do
      v_10986 <- getRegister v_2507;
      v_10988 <- evaluateAddress v_2506;
      v_10989 <- load v_10988 16;
      setRegister (lhs.of_reg v_2507) (concat (mux (sgt (extract v_10986 0 16) (extract v_10989 0 16)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_10986 16 32) (extract v_10989 16 32)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_10986 32 48) (extract v_10989 32 48)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_10986 48 64) (extract v_10989 48 64)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_10986 64 80) (extract v_10989 64 80)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_10986 80 96) (extract v_10989 80 96)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (sgt (extract v_10986 96 112) (extract v_10989 96 112)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (mux (sgt (extract v_10986 112 128) (extract v_10989 112 128)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)))))))));
      pure ()
    pat_end
