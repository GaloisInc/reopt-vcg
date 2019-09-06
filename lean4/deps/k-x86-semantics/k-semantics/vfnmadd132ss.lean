def vfnmadd132ss1 : instruction :=
  definst "vfnmadd132ss" $ do
    pattern fun (v_3222 : reg (bv 128)) (v_3223 : reg (bv 128)) (v_3224 : reg (bv 128)) => do
      v_7005 <- getRegister v_3224;
      v_7008 <- getRegister v_3223;
      v_7010 <- getRegister v_3222;
      setRegister (lhs.of_reg v_3224) (concat (extract v_7005 0 96) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7005 96 128) (extract v_7008 96 128) (extract v_7010 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3219 : Mem) (v_3217 : reg (bv 128)) (v_3218 : reg (bv 128)) => do
      v_12766 <- getRegister v_3218;
      v_12769 <- getRegister v_3217;
      v_12771 <- evaluateAddress v_3219;
      v_12772 <- load v_12771 4;
      setRegister (lhs.of_reg v_3218) (concat (extract v_12766 0 96) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12766 96 128) (extract v_12769 96 128) v_12772));
      pure ()
    pat_end
