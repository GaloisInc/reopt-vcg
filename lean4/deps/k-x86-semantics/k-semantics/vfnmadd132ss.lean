def vfnmadd132ss1 : instruction :=
  definst "vfnmadd132ss" $ do
    pattern fun (v_3146 : reg (bv 128)) (v_3147 : reg (bv 128)) (v_3148 : reg (bv 128)) => do
      v_10685 <- getRegister v_3148;
      v_10688 <- getRegister v_3147;
      v_10690 <- getRegister v_3146;
      setRegister (lhs.of_reg v_3148) (concat (extract v_10685 0 96) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10685 96 128) (extract v_10688 96 128) (extract v_10690 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3143 : Mem) (v_3141 : reg (bv 128)) (v_3142 : reg (bv 128)) => do
      v_21361 <- getRegister v_3142;
      v_21364 <- getRegister v_3141;
      v_21366 <- evaluateAddress v_3143;
      v_21367 <- load v_21366 4;
      setRegister (lhs.of_reg v_3142) (concat (extract v_21361 0 96) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21361 96 128) (extract v_21364 96 128) v_21367));
      pure ()
    pat_end
