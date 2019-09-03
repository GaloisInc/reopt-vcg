def vpmaskmovq1 : instruction :=
  definst "vpmaskmovq" $ do
    pattern fun (v_3426 : Mem) (v_3422 : reg (bv 128)) (v_3423 : reg (bv 128)) => do
      v_19161 <- getRegister v_3422;
      v_19164 <- evaluateAddress v_3426;
      v_19165 <- load v_19164 16;
      setRegister (lhs.of_reg v_3423) (concat (mux (eq (extract v_19161 0 1) (expression.bv_nat 1 1)) (extract v_19165 0 64) (expression.bv_nat 64 0)) (mux (eq (extract v_19161 64 65) (expression.bv_nat 1 1)) (extract v_19165 64 128) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3429 : Mem) (v_3430 : reg (bv 256)) (v_3431 : reg (bv 256)) => do
      v_19174 <- getRegister v_3430;
      v_19177 <- evaluateAddress v_3429;
      v_19178 <- load v_19177 32;
      setRegister (lhs.of_reg v_3431) (concat (mux (eq (extract v_19174 0 1) (expression.bv_nat 1 1)) (extract v_19178 0 64) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_19174 64 65) (expression.bv_nat 1 1)) (extract v_19178 64 128) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_19174 128 129) (expression.bv_nat 1 1)) (extract v_19178 128 192) (expression.bv_nat 64 0)) (mux (eq (extract v_19174 192 193) (expression.bv_nat 1 1)) (extract v_19178 192 256) (expression.bv_nat 64 0)))));
      pure ()
    pat_end;
    pattern fun (v_3412 : reg (bv 128)) (v_3413 : reg (bv 128)) (v_3416 : Mem) => do
      v_19759 <- evaluateAddress v_3416;
      v_19760 <- getRegister v_3413;
      v_19763 <- getRegister v_3412;
      v_19765 <- load v_19759 16;
      store v_19759 (concat (mux (eq (extract v_19760 0 1) (expression.bv_nat 1 1)) (extract v_19763 0 64) (extract v_19765 0 64)) (mux (eq (extract v_19760 64 65) (expression.bv_nat 1 1)) (extract v_19763 64 128) (extract v_19765 64 128))) 16;
      pure ()
    pat_end;
    pattern fun (v_3420 : reg (bv 256)) (v_3421 : reg (bv 256)) (v_3419 : Mem) => do
      v_19775 <- evaluateAddress v_3419;
      v_19776 <- getRegister v_3421;
      v_19779 <- getRegister v_3420;
      v_19781 <- load v_19775 32;
      store v_19775 (concat (mux (eq (extract v_19776 0 1) (expression.bv_nat 1 1)) (extract v_19779 0 64) (extract v_19781 0 64)) (concat (mux (eq (extract v_19776 64 65) (expression.bv_nat 1 1)) (extract v_19779 64 128) (extract v_19781 64 128)) (concat (mux (eq (extract v_19776 128 129) (expression.bv_nat 1 1)) (extract v_19779 128 192) (extract v_19781 128 192)) (mux (eq (extract v_19776 192 193) (expression.bv_nat 1 1)) (extract v_19779 192 256) (extract v_19781 192 256))))) 32;
      pure ()
    pat_end
