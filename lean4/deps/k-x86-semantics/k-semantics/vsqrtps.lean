def vsqrtps1 : instruction :=
  definst "vsqrtps" $ do
    pattern fun (v_3039 : reg (bv 128)) (v_3040 : reg (bv 128)) => do
      v_7031 <- getRegister v_3039;
      setRegister (lhs.of_reg v_3040) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_7031 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_7031 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_7031 64 96)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_7031 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3048 : reg (bv 256)) (v_3049 : reg (bv 256)) => do
      v_7048 <- getRegister v_3048;
      setRegister (lhs.of_reg v_3049) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_7048 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_7048 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_7048 64 96)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_7048 96 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_7048 128 160)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_7048 160 192)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_7048 192 224)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_7048 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_3034 : Mem) (v_3035 : reg (bv 128)) => do
      v_12974 <- evaluateAddress v_3034;
      v_12975 <- load v_12974 16;
      setRegister (lhs.of_reg v_3035) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12975 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12975 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12975 64 96)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12975 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3043 : Mem) (v_3044 : reg (bv 256)) => do
      v_12988 <- evaluateAddress v_3043;
      v_12989 <- load v_12988 32;
      setRegister (lhs.of_reg v_3044) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12989 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12989 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12989 64 96)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12989 96 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12989 128 160)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12989 160 192)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12989 192 224)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12989 224 256)))))))));
      pure ()
    pat_end
