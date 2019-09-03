def sqrtps1 : instruction :=
  definst "sqrtps" $ do
    pattern fun (v_3066 : reg (bv 128)) (v_3067 : reg (bv 128)) => do
      v_6739 <- getRegister v_3066;
      setRegister (lhs.of_reg v_3067) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6739 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6739 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6739 64 96)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6739 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3061 : Mem) (v_3062 : reg (bv 128)) => do
      v_10257 <- evaluateAddress v_3061;
      v_10258 <- load v_10257 16;
      setRegister (lhs.of_reg v_3062) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_10258 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_10258 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_10258 64 96)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_10258 96 128)))));
      pure ()
    pat_end
