def vfnmadd213ss1 : instruction :=
  definst "vfnmadd213ss" $ do
    pattern fun (v_3212 : reg (bv 128)) (v_3213 : reg (bv 128)) (v_3214 : reg (bv 128)) => do
      v_10837 <- getRegister v_3214;
      v_10840 <- getRegister v_3213;
      v_10842 <- getRegister v_3212;
      setRegister (lhs.of_reg v_3214) (concat (extract v_10837 0 96) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd213_single (extract v_10837 96 128) (extract v_10840 96 128) (extract v_10842 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3209 : Mem) (v_3207 : reg (bv 128)) (v_3208 : reg (bv 128)) => do
      v_21487 <- getRegister v_3208;
      v_21490 <- getRegister v_3207;
      v_21492 <- evaluateAddress v_3209;
      v_21493 <- load v_21492 4;
      setRegister (lhs.of_reg v_3208) (concat (extract v_21487 0 96) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd213_single (extract v_21487 96 128) (extract v_21490 96 128) v_21493));
      pure ()
    pat_end
