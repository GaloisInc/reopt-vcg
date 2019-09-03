def vpermilpd1 : instruction :=
  definst "vpermilpd" $ do
    pattern fun (v_2987 : imm int) (v_2983 : reg (bv 128)) (v_2984 : reg (bv 128)) => do
      v_8267 <- eval (handleImmediateWithSignExtend v_2987 8 8);
      v_8270 <- getRegister v_2983;
      v_8271 <- eval (extract v_8270 64 128);
      v_8272 <- eval (extract v_8270 0 64);
      setRegister (lhs.of_reg v_2984) (concat (mux (eq (extract v_8267 6 7) (expression.bv_nat 1 0)) v_8271 v_8272) (mux (eq (extract v_8267 7 8) (expression.bv_nat 1 0)) v_8271 v_8272));
      pure ()
    pat_end;
    pattern fun (v_2994 : reg (bv 128)) (v_2995 : reg (bv 128)) (v_2996 : reg (bv 128)) => do
      v_8284 <- getRegister v_2994;
      v_8287 <- getRegister v_2995;
      v_8288 <- eval (extract v_8287 64 128);
      v_8289 <- eval (extract v_8287 0 64);
      setRegister (lhs.of_reg v_2996) (concat (mux (eq (extract v_8284 62 63) (expression.bv_nat 1 0)) v_8288 v_8289) (mux (eq (extract v_8284 126 127) (expression.bv_nat 1 0)) v_8288 v_8289));
      pure ()
    pat_end;
    pattern fun (v_3007 : imm int) (v_3009 : reg (bv 256)) (v_3010 : reg (bv 256)) => do
      v_8301 <- eval (handleImmediateWithSignExtend v_3007 8 8);
      v_8304 <- getRegister v_3009;
      v_8305 <- eval (extract v_8304 64 128);
      v_8306 <- eval (extract v_8304 0 64);
      v_8313 <- eval (extract v_8304 192 256);
      v_8314 <- eval (extract v_8304 128 192);
      setRegister (lhs.of_reg v_3010) (concat (mux (eq (extract v_8301 4 5) (expression.bv_nat 1 0)) v_8305 v_8306) (concat (mux (eq (extract v_8301 5 6) (expression.bv_nat 1 0)) v_8305 v_8306) (concat (mux (eq (extract v_8301 6 7) (expression.bv_nat 1 0)) v_8313 v_8314) (mux (eq (extract v_8301 7 8) (expression.bv_nat 1 0)) v_8313 v_8314))));
      pure ()
    pat_end;
    pattern fun (v_3019 : reg (bv 256)) (v_3020 : reg (bv 256)) (v_3021 : reg (bv 256)) => do
      v_8328 <- getRegister v_3019;
      v_8331 <- getRegister v_3020;
      v_8332 <- eval (extract v_8331 64 128);
      v_8333 <- eval (extract v_8331 0 64);
      v_8340 <- eval (extract v_8331 192 256);
      v_8341 <- eval (extract v_8331 128 192);
      setRegister (lhs.of_reg v_3021) (concat (mux (eq (extract v_8328 62 63) (expression.bv_nat 1 0)) v_8332 v_8333) (concat (mux (eq (extract v_8328 126 127) (expression.bv_nat 1 0)) v_8332 v_8333) (concat (mux (eq (extract v_8328 190 191) (expression.bv_nat 1 0)) v_8340 v_8341) (mux (eq (extract v_8328 254 255) (expression.bv_nat 1 0)) v_8340 v_8341))));
      pure ()
    pat_end;
    pattern fun (v_2982 : imm int) (v_2981 : Mem) (v_2978 : reg (bv 128)) => do
      v_17053 <- eval (handleImmediateWithSignExtend v_2982 8 8);
      v_17056 <- evaluateAddress v_2981;
      v_17057 <- load v_17056 16;
      v_17058 <- eval (extract v_17057 64 128);
      v_17059 <- eval (extract v_17057 0 64);
      setRegister (lhs.of_reg v_2978) (concat (mux (eq (extract v_17053 6 7) (expression.bv_nat 1 0)) v_17058 v_17059) (mux (eq (extract v_17053 7 8) (expression.bv_nat 1 0)) v_17058 v_17059));
      pure ()
    pat_end;
    pattern fun (v_2993 : Mem) (v_2989 : reg (bv 128)) (v_2990 : reg (bv 128)) => do
      v_17066 <- evaluateAddress v_2993;
      v_17067 <- load v_17066 16;
      v_17070 <- getRegister v_2989;
      v_17071 <- eval (extract v_17070 64 128);
      v_17072 <- eval (extract v_17070 0 64);
      setRegister (lhs.of_reg v_2990) (concat (mux (eq (extract v_17067 62 63) (expression.bv_nat 1 0)) v_17071 v_17072) (mux (eq (extract v_17067 126 127) (expression.bv_nat 1 0)) v_17071 v_17072));
      pure ()
    pat_end;
    pattern fun (v_3003 : imm int) (v_3002 : Mem) (v_3004 : reg (bv 256)) => do
      v_17079 <- eval (handleImmediateWithSignExtend v_3003 8 8);
      v_17082 <- evaluateAddress v_3002;
      v_17083 <- load v_17082 32;
      v_17084 <- eval (extract v_17083 64 128);
      v_17085 <- eval (extract v_17083 0 64);
      v_17092 <- eval (extract v_17083 192 256);
      v_17093 <- eval (extract v_17083 128 192);
      setRegister (lhs.of_reg v_3004) (concat (mux (eq (extract v_17079 4 5) (expression.bv_nat 1 0)) v_17084 v_17085) (concat (mux (eq (extract v_17079 5 6) (expression.bv_nat 1 0)) v_17084 v_17085) (concat (mux (eq (extract v_17079 6 7) (expression.bv_nat 1 0)) v_17092 v_17093) (mux (eq (extract v_17079 7 8) (expression.bv_nat 1 0)) v_17092 v_17093))));
      pure ()
    pat_end;
    pattern fun (v_3013 : Mem) (v_3014 : reg (bv 256)) (v_3015 : reg (bv 256)) => do
      v_17102 <- evaluateAddress v_3013;
      v_17103 <- load v_17102 32;
      v_17106 <- getRegister v_3014;
      v_17107 <- eval (extract v_17106 64 128);
      v_17108 <- eval (extract v_17106 0 64);
      v_17115 <- eval (extract v_17106 192 256);
      v_17116 <- eval (extract v_17106 128 192);
      setRegister (lhs.of_reg v_3015) (concat (mux (eq (extract v_17103 62 63) (expression.bv_nat 1 0)) v_17107 v_17108) (concat (mux (eq (extract v_17103 126 127) (expression.bv_nat 1 0)) v_17107 v_17108) (concat (mux (eq (extract v_17103 190 191) (expression.bv_nat 1 0)) v_17115 v_17116) (mux (eq (extract v_17103 254 255) (expression.bv_nat 1 0)) v_17115 v_17116))));
      pure ()
    pat_end
