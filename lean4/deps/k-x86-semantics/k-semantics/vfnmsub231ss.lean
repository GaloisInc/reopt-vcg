def vfnmsub231ss1 : instruction :=
  definst "vfnmsub231ss" $ do
    pattern fun (v_3552 : reg (bv 128)) (v_3553 : reg (bv 128)) (v_3554 : reg (bv 128)) => do
      v_8153 <- getRegister v_3554;
      v_8155 <- getRegister v_3553;
      v_8158 <- getRegister v_3552;
      setRegister (lhs.of_reg v_3554) (concat (extract v_8153 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_8155 96 128) 24 8) (MInt2Float (extract v_8158 96 128) 24 8))) (MInt2Float (extract v_8153 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_3549 : Mem) (v_3547 : reg (bv 128)) (v_3548 : reg (bv 128)) => do
      v_13784 <- getRegister v_3548;
      v_13786 <- getRegister v_3547;
      v_13789 <- evaluateAddress v_3549;
      v_13790 <- load v_13789 4;
      setRegister (lhs.of_reg v_3548) (concat (extract v_13784 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13786 96 128) 24 8) (MInt2Float v_13790 24 8))) (MInt2Float (extract v_13784 96 128) 24 8)) 32));
      pure ()
    pat_end
