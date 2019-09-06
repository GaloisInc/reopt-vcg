def sqrtps1 : instruction :=
  definst "sqrtps" $ do
    pattern fun (v_3157 : reg (bv 128)) (v_3158 : reg (bv 128)) => do
      v_5485 <- getRegister v_3157;
      setRegister (lhs.of_reg v_3158) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_5485 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_5485 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_5485 64 96)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_5485 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3153 : Mem) (v_3154 : reg (bv 128)) => do
      v_8545 <- evaluateAddress v_3153;
      v_8546 <- load v_8545 16;
      setRegister (lhs.of_reg v_3154) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_8546 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_8546 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_8546 64 96)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_8546 96 128)))));
      pure ()
    pat_end
