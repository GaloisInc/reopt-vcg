def sqrtps1 : instruction :=
  definst "sqrtps" $ do
    pattern fun (v_3079 : reg (bv 128)) (v_3080 : reg (bv 128)) => do
      v_6735 <- getRegister v_3079;
      setRegister (lhs.of_reg v_3080) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6735 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6735 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6735 64 96)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6735 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3074 : Mem) (v_3075 : reg (bv 128)) => do
      v_10279 <- evaluateAddress v_3074;
      v_10280 <- load v_10279 16;
      setRegister (lhs.of_reg v_3075) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_10280 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_10280 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_10280 64 96)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_10280 96 128)))));
      pure ()
    pat_end
