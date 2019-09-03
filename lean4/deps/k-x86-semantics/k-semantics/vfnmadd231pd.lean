def vfnmadd231pd1 : instruction :=
  definst "vfnmadd231pd" $ do
    pattern fun (v_3223 : reg (bv 128)) (v_3224 : reg (bv 128)) (v_3225 : reg (bv 128)) => do
      v_10852 <- getRegister v_3224;
      v_10854 <- getRegister v_3225;
      v_10856 <- getRegister v_3223;
      setRegister (lhs.of_reg v_3225) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_10852 0 64) (extract v_10854 0 64) (extract v_10856 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_10852 64 128) (extract v_10854 64 128) (extract v_10856 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3234 : reg (bv 256)) (v_3235 : reg (bv 256)) (v_3236 : reg (bv 256)) => do
      v_10870 <- getRegister v_3235;
      v_10872 <- getRegister v_3236;
      v_10874 <- getRegister v_3234;
      setRegister (lhs.of_reg v_3236) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_10870 0 64) (extract v_10872 0 64) (extract v_10874 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_10870 64 128) (extract v_10872 64 128) (extract v_10874 64 128))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_10870 128 192) (extract v_10872 128 192) (extract v_10874 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_10870 192 256) (extract v_10872 192 256) (extract v_10874 192 256))));
      pure ()
    pat_end;
    pattern fun (v_3220 : Mem) (v_3218 : reg (bv 128)) (v_3219 : reg (bv 128)) => do
      v_21497 <- getRegister v_3218;
      v_21499 <- getRegister v_3219;
      v_21501 <- evaluateAddress v_3220;
      v_21502 <- load v_21501 16;
      setRegister (lhs.of_reg v_3219) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_21497 0 64) (extract v_21499 0 64) (extract v_21502 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_21497 64 128) (extract v_21499 64 128) (extract v_21502 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3229 : Mem) (v_3230 : reg (bv 256)) (v_3231 : reg (bv 256)) => do
      v_21511 <- getRegister v_3230;
      v_21513 <- getRegister v_3231;
      v_21515 <- evaluateAddress v_3229;
      v_21516 <- load v_21515 32;
      setRegister (lhs.of_reg v_3231) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_21511 0 64) (extract v_21513 0 64) (extract v_21516 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_21511 64 128) (extract v_21513 64 128) (extract v_21516 64 128))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_21511 128 192) (extract v_21513 128 192) (extract v_21516 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_21511 192 256) (extract v_21513 192 256) (extract v_21516 192 256))));
      pure ()
    pat_end
