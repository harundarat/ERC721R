const { buildModule } = require("@nomicfoundation/hardhat-ignition/modules");

module.exports = buildModule("NFTRModule", (m) => {
    const nftr = m.contract("NFTR", [], {});

    return { nftr };
});