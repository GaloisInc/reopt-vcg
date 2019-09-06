def vunpckhpd1 : instruction :=
  definst "vunpckhpd" $ do
    pattern fun (v_3227 : reg (bv 128)) (v_3228 : reg (bv 128)) (v_3229 : reg (bv 128)) => do
      v_7543 <- getRegister v_3227;
      v_7545 <- getRegister v_3228;
      setRegister (lhs.of_reg v_3229) (concat (extract v_7543 0 64) (extract v_7545 0 64));
      pure ()
    pat_end;
    pattern fun (v_3238 : reg (bv 256)) (v_3239 : reg (bv 256)) (v_3240 : reg (bv 256)) => do
      v_7554 <- getRegister v_3238;
      v_7556 <- getRegister v_3239;
      setRegister (lhs.of_reg v_3240) (concat (concat (extract v_7554 0 64) (extract v_7556 0 64)) (concat (extract v_7554 128 192) (extract v_7556 128 192)));
      pure ()
    pat_end;
    pattern fun (v_3221 : Mem) (v_3222 : reg (bv 128)) (v_3223 : reg (bv 128)) => do
      v_13423 <- evaluateAddress v_3221;
      v_13424 <- load v_13423 16;
      v_13426 <- getRegister v_3222;
      setRegister (lhs.of_reg v_3223) (concat (extract v_13424 0 64) (extract v_13426 0 64));
      pure ()
    pat_end;
    pattern fun (v_3232 : Mem) (v_3233 : reg (bv 256)) (v_3234 : reg (bv 256)) => do
      v_13430 <- evaluateAddress v_3232;
      v_13431 <- load v_13430 32;
      v_13433 <- getRegister v_3233;
      setRegister (lhs.of_reg v_3234) (concat (concat (extract v_13431 0 64) (extract v_13433 0 64)) (concat (extract v_13431 128 192) (extract v_13433 128 192)));
      pure ()
    pat_end
