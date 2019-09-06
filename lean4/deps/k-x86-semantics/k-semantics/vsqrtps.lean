def vsqrtps1 : instruction :=
  definst "vsqrtps" $ do
    pattern fun (v_3066 : reg (bv 128)) (v_3067 : reg (bv 128)) => do
      v_7058 <- getRegister v_3066;
      setRegister (lhs.of_reg v_3067) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_7058 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_7058 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_7058 64 96)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_7058 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3075 : reg (bv 256)) (v_3076 : reg (bv 256)) => do
      v_7075 <- getRegister v_3075;
      setRegister (lhs.of_reg v_3076) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_7075 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_7075 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_7075 64 96)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_7075 96 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_7075 128 160)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_7075 160 192)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_7075 192 224)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_7075 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_3061 : Mem) (v_3062 : reg (bv 128)) => do
      v_13001 <- evaluateAddress v_3061;
      v_13002 <- load v_13001 16;
      setRegister (lhs.of_reg v_3062) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_13002 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_13002 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_13002 64 96)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_13002 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3070 : Mem) (v_3071 : reg (bv 256)) => do
      v_13015 <- evaluateAddress v_3070;
      v_13016 <- load v_13015 32;
      setRegister (lhs.of_reg v_3071) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_13016 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_13016 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_13016 64 96)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_13016 96 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_13016 128 160)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_13016 160 192)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_13016 192 224)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_13016 224 256)))))))));
      pure ()
    pat_end
