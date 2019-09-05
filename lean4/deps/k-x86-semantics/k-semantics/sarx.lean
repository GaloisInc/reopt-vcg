def sarx1 : instruction :=
  definst "sarx" $ do
    pattern fun (v_3204 : reg (bv 32)) (v_3205 : reg (bv 32)) (v_3206 : reg (bv 32)) => do
      v_8585 <- getRegister v_3205;
      v_8586 <- getRegister v_3204;
      setRegister (lhs.of_reg v_3206) (ashr v_8585 (bv_and v_8586 (expression.bv_nat 32 31)));
      pure ()
    pat_end;
    pattern fun (v_3225 : reg (bv 64)) (v_3226 : reg (bv 64)) (v_3227 : reg (bv 64)) => do
      v_8601 <- getRegister v_3226;
      v_8602 <- getRegister v_3225;
      setRegister (lhs.of_reg v_3227) (ashr v_8601 (bv_and v_8602 (expression.bv_nat 64 63)));
      pure ()
    pat_end;
    pattern fun (v_3194 : reg (bv 32)) (v_3196 : Mem) (v_3195 : reg (bv 32)) => do
      v_14127 <- evaluateAddress v_3196;
      v_14128 <- load v_14127 4;
      v_14129 <- getRegister v_3194;
      setRegister (lhs.of_reg v_3195) (ashr v_14128 (bv_and v_14129 (expression.bv_nat 32 31)));
      pure ()
    pat_end;
    pattern fun (v_3215 : reg (bv 64)) (v_3217 : Mem) (v_3216 : reg (bv 64)) => do
      v_14133 <- evaluateAddress v_3217;
      v_14134 <- load v_14133 8;
      v_14135 <- getRegister v_3215;
      setRegister (lhs.of_reg v_3216) (ashr v_14134 (bv_and v_14135 (expression.bv_nat 64 63)));
      pure ()
    pat_end
