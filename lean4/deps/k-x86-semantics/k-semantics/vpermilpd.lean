def vpermilpd1 : instruction :=
  definst "vpermilpd" $ do
    pattern fun (v_2970 : imm int) (v_2974 : reg (bv 128)) (v_2975 : reg (bv 128)) => do
      v_8404 <- eval (handleImmediateWithSignExtend v_2970 8 8);
      v_8407 <- getRegister v_2974;
      v_8408 <- eval (extract v_8407 64 128);
      v_8409 <- eval (extract v_8407 0 64);
      setRegister (lhs.of_reg v_2975) (concat (mux (eq (extract v_8404 6 7) (expression.bv_nat 1 0)) v_8408 v_8409) (mux (eq (extract v_8404 7 8) (expression.bv_nat 1 0)) v_8408 v_8409));
      pure ()
    pat_end;
    pattern fun (v_2984 : reg (bv 128)) (v_2985 : reg (bv 128)) (v_2986 : reg (bv 128)) => do
      v_8421 <- getRegister v_2984;
      v_8424 <- getRegister v_2985;
      v_8425 <- eval (extract v_8424 64 128);
      v_8426 <- eval (extract v_8424 0 64);
      setRegister (lhs.of_reg v_2986) (concat (mux (eq (extract v_8421 62 63) (expression.bv_nat 1 0)) v_8425 v_8426) (mux (eq (extract v_8421 126 127) (expression.bv_nat 1 0)) v_8425 v_8426));
      pure ()
    pat_end;
    pattern fun (v_2992 : imm int) (v_2996 : reg (bv 256)) (v_2997 : reg (bv 256)) => do
      v_8438 <- eval (handleImmediateWithSignExtend v_2992 8 8);
      v_8441 <- getRegister v_2996;
      v_8442 <- eval (extract v_8441 64 128);
      v_8443 <- eval (extract v_8441 0 64);
      v_8450 <- eval (extract v_8441 192 256);
      v_8451 <- eval (extract v_8441 128 192);
      setRegister (lhs.of_reg v_2997) (concat (mux (eq (extract v_8438 4 5) (expression.bv_nat 1 0)) v_8442 v_8443) (concat (mux (eq (extract v_8438 5 6) (expression.bv_nat 1 0)) v_8442 v_8443) (concat (mux (eq (extract v_8438 6 7) (expression.bv_nat 1 0)) v_8450 v_8451) (mux (eq (extract v_8438 7 8) (expression.bv_nat 1 0)) v_8450 v_8451))));
      pure ()
    pat_end;
    pattern fun (v_3006 : reg (bv 256)) (v_3007 : reg (bv 256)) (v_3008 : reg (bv 256)) => do
      v_8465 <- getRegister v_3006;
      v_8468 <- getRegister v_3007;
      v_8469 <- eval (extract v_8468 64 128);
      v_8470 <- eval (extract v_8468 0 64);
      v_8477 <- eval (extract v_8468 192 256);
      v_8478 <- eval (extract v_8468 128 192);
      setRegister (lhs.of_reg v_3008) (concat (mux (eq (extract v_8465 62 63) (expression.bv_nat 1 0)) v_8469 v_8470) (concat (mux (eq (extract v_8465 126 127) (expression.bv_nat 1 0)) v_8469 v_8470) (concat (mux (eq (extract v_8465 190 191) (expression.bv_nat 1 0)) v_8477 v_8478) (mux (eq (extract v_8465 254 255) (expression.bv_nat 1 0)) v_8477 v_8478))));
      pure ()
    pat_end;
    pattern fun (v_2965 : imm int) (v_2968 : Mem) (v_2969 : reg (bv 128)) => do
      v_17562 <- eval (handleImmediateWithSignExtend v_2965 8 8);
      v_17565 <- evaluateAddress v_2968;
      v_17566 <- load v_17565 16;
      v_17567 <- eval (extract v_17566 64 128);
      v_17568 <- eval (extract v_17566 0 64);
      setRegister (lhs.of_reg v_2969) (concat (mux (eq (extract v_17562 6 7) (expression.bv_nat 1 0)) v_17567 v_17568) (mux (eq (extract v_17562 7 8) (expression.bv_nat 1 0)) v_17567 v_17568));
      pure ()
    pat_end;
    pattern fun (v_2978 : Mem) (v_2979 : reg (bv 128)) (v_2980 : reg (bv 128)) => do
      v_17575 <- evaluateAddress v_2978;
      v_17576 <- load v_17575 16;
      v_17579 <- getRegister v_2979;
      v_17580 <- eval (extract v_17579 64 128);
      v_17581 <- eval (extract v_17579 0 64);
      setRegister (lhs.of_reg v_2980) (concat (mux (eq (extract v_17576 62 63) (expression.bv_nat 1 0)) v_17580 v_17581) (mux (eq (extract v_17576 126 127) (expression.bv_nat 1 0)) v_17580 v_17581));
      pure ()
    pat_end;
    pattern fun (v_2987 : imm int) (v_2990 : Mem) (v_2991 : reg (bv 256)) => do
      v_17588 <- eval (handleImmediateWithSignExtend v_2987 8 8);
      v_17591 <- evaluateAddress v_2990;
      v_17592 <- load v_17591 32;
      v_17593 <- eval (extract v_17592 64 128);
      v_17594 <- eval (extract v_17592 0 64);
      v_17601 <- eval (extract v_17592 192 256);
      v_17602 <- eval (extract v_17592 128 192);
      setRegister (lhs.of_reg v_2991) (concat (mux (eq (extract v_17588 4 5) (expression.bv_nat 1 0)) v_17593 v_17594) (concat (mux (eq (extract v_17588 5 6) (expression.bv_nat 1 0)) v_17593 v_17594) (concat (mux (eq (extract v_17588 6 7) (expression.bv_nat 1 0)) v_17601 v_17602) (mux (eq (extract v_17588 7 8) (expression.bv_nat 1 0)) v_17601 v_17602))));
      pure ()
    pat_end;
    pattern fun (v_3000 : Mem) (v_3001 : reg (bv 256)) (v_3002 : reg (bv 256)) => do
      v_17611 <- evaluateAddress v_3000;
      v_17612 <- load v_17611 32;
      v_17615 <- getRegister v_3001;
      v_17616 <- eval (extract v_17615 64 128);
      v_17617 <- eval (extract v_17615 0 64);
      v_17624 <- eval (extract v_17615 192 256);
      v_17625 <- eval (extract v_17615 128 192);
      setRegister (lhs.of_reg v_3002) (concat (mux (eq (extract v_17612 62 63) (expression.bv_nat 1 0)) v_17616 v_17617) (concat (mux (eq (extract v_17612 126 127) (expression.bv_nat 1 0)) v_17616 v_17617) (concat (mux (eq (extract v_17612 190 191) (expression.bv_nat 1 0)) v_17624 v_17625) (mux (eq (extract v_17612 254 255) (expression.bv_nat 1 0)) v_17624 v_17625))));
      pure ()
    pat_end
