def vunpckhpd1 : instruction :=
  definst "vunpckhpd" $ do
    pattern fun (v_3200 : reg (bv 128)) (v_3201 : reg (bv 128)) (v_3202 : reg (bv 128)) => do
      v_7516 <- getRegister v_3200;
      v_7518 <- getRegister v_3201;
      setRegister (lhs.of_reg v_3202) (concat (extract v_7516 0 64) (extract v_7518 0 64));
      pure ()
    pat_end;
    pattern fun (v_3211 : reg (bv 256)) (v_3212 : reg (bv 256)) (v_3213 : reg (bv 256)) => do
      v_7527 <- getRegister v_3211;
      v_7529 <- getRegister v_3212;
      setRegister (lhs.of_reg v_3213) (concat (concat (extract v_7527 0 64) (extract v_7529 0 64)) (concat (extract v_7527 128 192) (extract v_7529 128 192)));
      pure ()
    pat_end;
    pattern fun (v_3194 : Mem) (v_3195 : reg (bv 128)) (v_3196 : reg (bv 128)) => do
      v_13396 <- evaluateAddress v_3194;
      v_13397 <- load v_13396 16;
      v_13399 <- getRegister v_3195;
      setRegister (lhs.of_reg v_3196) (concat (extract v_13397 0 64) (extract v_13399 0 64));
      pure ()
    pat_end;
    pattern fun (v_3205 : Mem) (v_3206 : reg (bv 256)) (v_3207 : reg (bv 256)) => do
      v_13403 <- evaluateAddress v_3205;
      v_13404 <- load v_13403 32;
      v_13406 <- getRegister v_3206;
      setRegister (lhs.of_reg v_3207) (concat (concat (extract v_13404 0 64) (extract v_13406 0 64)) (concat (extract v_13404 128 192) (extract v_13406 128 192)));
      pure ()
    pat_end
