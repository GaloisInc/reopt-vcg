def vpsravd1 : instruction :=
  definst "vpsravd" $ do
    pattern fun (v_3243 : reg (bv 128)) (v_3244 : reg (bv 128)) (v_3245 : reg (bv 128)) => do
      v_8372 <- getRegister v_3244;
      v_8376 <- getRegister v_3243;
      setRegister (lhs.of_reg v_3245) (concat (ashr (mi 32 (svalueMInt (extract v_8372 0 32))) (uvalueMInt (extract v_8376 0 32))) (concat (ashr (mi 32 (svalueMInt (extract v_8372 32 64))) (uvalueMInt (extract v_8376 32 64))) (concat (ashr (mi 32 (svalueMInt (extract v_8372 64 96))) (uvalueMInt (extract v_8376 64 96))) (ashr (mi 32 (svalueMInt (extract v_8372 96 128))) (uvalueMInt (extract v_8376 96 128))))));
      pure ()
    pat_end;
    pattern fun (v_3255 : reg (bv 256)) (v_3256 : reg (bv 256)) (v_3257 : reg (bv 256)) => do
      v_8407 <- getRegister v_3256;
      v_8411 <- getRegister v_3255;
      setRegister (lhs.of_reg v_3257) (concat (ashr (mi 32 (svalueMInt (extract v_8407 0 32))) (uvalueMInt (extract v_8411 0 32))) (concat (ashr (mi 32 (svalueMInt (extract v_8407 32 64))) (uvalueMInt (extract v_8411 32 64))) (concat (ashr (mi 32 (svalueMInt (extract v_8407 64 96))) (uvalueMInt (extract v_8411 64 96))) (concat (ashr (mi 32 (svalueMInt (extract v_8407 96 128))) (uvalueMInt (extract v_8411 96 128))) (concat (ashr (mi 32 (svalueMInt (extract v_8407 128 160))) (uvalueMInt (extract v_8411 128 160))) (concat (ashr (mi 32 (svalueMInt (extract v_8407 160 192))) (uvalueMInt (extract v_8411 160 192))) (concat (ashr (mi 32 (svalueMInt (extract v_8407 192 224))) (uvalueMInt (extract v_8411 192 224))) (ashr (mi 32 (svalueMInt (extract v_8407 224 256))) (uvalueMInt (extract v_8411 224 256))))))))));
      pure ()
    pat_end;
    pattern fun (v_3237 : Mem) (v_3238 : reg (bv 128)) (v_3239 : reg (bv 128)) => do
      v_14543 <- getRegister v_3238;
      v_14547 <- evaluateAddress v_3237;
      v_14548 <- load v_14547 16;
      setRegister (lhs.of_reg v_3239) (concat (ashr (mi 32 (svalueMInt (extract v_14543 0 32))) (uvalueMInt (extract v_14548 0 32))) (concat (ashr (mi 32 (svalueMInt (extract v_14543 32 64))) (uvalueMInt (extract v_14548 32 64))) (concat (ashr (mi 32 (svalueMInt (extract v_14543 64 96))) (uvalueMInt (extract v_14548 64 96))) (ashr (mi 32 (svalueMInt (extract v_14543 96 128))) (uvalueMInt (extract v_14548 96 128))))));
      pure ()
    pat_end;
    pattern fun (v_3248 : Mem) (v_3250 : reg (bv 256)) (v_3251 : reg (bv 256)) => do
      v_14574 <- getRegister v_3250;
      v_14578 <- evaluateAddress v_3248;
      v_14579 <- load v_14578 32;
      setRegister (lhs.of_reg v_3251) (concat (ashr (mi 32 (svalueMInt (extract v_14574 0 32))) (uvalueMInt (extract v_14579 0 32))) (concat (ashr (mi 32 (svalueMInt (extract v_14574 32 64))) (uvalueMInt (extract v_14579 32 64))) (concat (ashr (mi 32 (svalueMInt (extract v_14574 64 96))) (uvalueMInt (extract v_14579 64 96))) (concat (ashr (mi 32 (svalueMInt (extract v_14574 96 128))) (uvalueMInt (extract v_14579 96 128))) (concat (ashr (mi 32 (svalueMInt (extract v_14574 128 160))) (uvalueMInt (extract v_14579 128 160))) (concat (ashr (mi 32 (svalueMInt (extract v_14574 160 192))) (uvalueMInt (extract v_14579 160 192))) (concat (ashr (mi 32 (svalueMInt (extract v_14574 192 224))) (uvalueMInt (extract v_14579 192 224))) (ashr (mi 32 (svalueMInt (extract v_14574 224 256))) (uvalueMInt (extract v_14579 224 256))))))))));
      pure ()
    pat_end
