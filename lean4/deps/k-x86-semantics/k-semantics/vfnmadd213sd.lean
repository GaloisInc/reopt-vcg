def vfnmadd213sd1 : instruction :=
  definst "vfnmadd213sd" $ do
    pattern fun (v_3201 : reg (bv 128)) (v_3202 : reg (bv 128)) (v_3203 : reg (bv 128)) => do
      v_10822 <- getRegister v_3203;
      v_10825 <- getRegister v_3202;
      v_10827 <- getRegister v_3201;
      setRegister (lhs.of_reg v_3203) (concat (extract v_10822 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd213_double (extract v_10822 64 128) (extract v_10825 64 128) (extract v_10827 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3198 : Mem) (v_3196 : reg (bv 128)) (v_3197 : reg (bv 128)) => do
      v_21477 <- getRegister v_3197;
      v_21480 <- getRegister v_3196;
      v_21482 <- evaluateAddress v_3198;
      v_21483 <- load v_21482 8;
      setRegister (lhs.of_reg v_3197) (concat (extract v_21477 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd213_double (extract v_21477 64 128) (extract v_21480 64 128) v_21483));
      pure ()
    pat_end
