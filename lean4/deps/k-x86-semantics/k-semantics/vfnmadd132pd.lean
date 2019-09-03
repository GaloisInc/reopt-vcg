def vfnmadd132pd1 : instruction :=
  definst "vfnmadd132pd" $ do
    pattern fun (v_3091 : reg (bv 128)) (v_3092 : reg (bv 128)) (v_3093 : reg (bv 128)) => do
      v_10548 <- getRegister v_3093;
      v_10550 <- getRegister v_3092;
      v_10552 <- getRegister v_3091;
      setRegister (lhs.of_reg v_3093) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_10548 0 64) (extract v_10550 0 64) (extract v_10552 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_10548 64 128) (extract v_10550 64 128) (extract v_10552 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3102 : reg (bv 256)) (v_3103 : reg (bv 256)) (v_3104 : reg (bv 256)) => do
      v_10566 <- getRegister v_3104;
      v_10568 <- getRegister v_3103;
      v_10570 <- getRegister v_3102;
      setRegister (lhs.of_reg v_3104) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_10566 0 64) (extract v_10568 0 64) (extract v_10570 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_10566 64 128) (extract v_10568 64 128) (extract v_10570 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_10566 128 192) (extract v_10568 128 192) (extract v_10570 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_10566 192 256) (extract v_10568 192 256) (extract v_10570 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3088 : Mem) (v_3086 : reg (bv 128)) (v_3087 : reg (bv 128)) => do
      v_21245 <- getRegister v_3087;
      v_21247 <- getRegister v_3086;
      v_21249 <- evaluateAddress v_3088;
      v_21250 <- load v_21249 16;
      setRegister (lhs.of_reg v_3087) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_21245 0 64) (extract v_21247 0 64) (extract v_21250 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_21245 64 128) (extract v_21247 64 128) (extract v_21250 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3097 : Mem) (v_3098 : reg (bv 256)) (v_3099 : reg (bv 256)) => do
      v_21259 <- getRegister v_3099;
      v_21261 <- getRegister v_3098;
      v_21263 <- evaluateAddress v_3097;
      v_21264 <- load v_21263 32;
      setRegister (lhs.of_reg v_3099) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_21259 0 64) (extract v_21261 0 64) (extract v_21264 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_21259 64 128) (extract v_21261 64 128) (extract v_21264 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_21259 128 192) (extract v_21261 128 192) (extract v_21264 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_21259 192 256) (extract v_21261 192 256) (extract v_21264 192 256)))));
      pure ()
    pat_end
