def vpcmpgtq1 : instruction :=
  definst "vpcmpgtq" $ do
    pattern fun (v_2956 : reg (bv 128)) (v_2957 : reg (bv 128)) (v_2958 : reg (bv 128)) => do
      v_7857 <- getRegister v_2957;
      v_7859 <- getRegister v_2956;
      setRegister (lhs.of_reg v_2958) (concat (mux (sgt (extract v_7857 0 64) (extract v_7859 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (sgt (extract v_7857 64 128) (extract v_7859 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2966 : reg (bv 256)) (v_2967 : reg (bv 256)) (v_2968 : reg (bv 256)) => do
      v_7874 <- getRegister v_2967;
      v_7876 <- getRegister v_2966;
      setRegister (lhs.of_reg v_2968) (concat (mux (sgt (extract v_7874 0 64) (extract v_7876 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (sgt (extract v_7874 64 128) (extract v_7876 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (sgt (extract v_7874 128 192) (extract v_7876 128 192)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (sgt (extract v_7874 192 256) (extract v_7876 192 256)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end;
    pattern fun (v_2950 : Mem) (v_2951 : reg (bv 128)) (v_2952 : reg (bv 128)) => do
      v_16425 <- getRegister v_2951;
      v_16427 <- evaluateAddress v_2950;
      v_16428 <- load v_16427 16;
      setRegister (lhs.of_reg v_2952) (concat (mux (sgt (extract v_16425 0 64) (extract v_16428 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (sgt (extract v_16425 64 128) (extract v_16428 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2961 : Mem) (v_2962 : reg (bv 256)) (v_2963 : reg (bv 256)) => do
      v_16438 <- getRegister v_2962;
      v_16440 <- evaluateAddress v_2961;
      v_16441 <- load v_16440 32;
      setRegister (lhs.of_reg v_2963) (concat (mux (sgt (extract v_16438 0 64) (extract v_16441 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (sgt (extract v_16438 64 128) (extract v_16441 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (sgt (extract v_16438 128 192) (extract v_16441 128 192)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (sgt (extract v_16438 192 256) (extract v_16441 192 256)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end
