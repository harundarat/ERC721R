// SPDX-License-Identifier: MIT
pragma solidity 0.8.24;

import "./ERC721A.sol";
import "./IERC721R.sol";
import "@openzeppelin/contracts/access/Ownable.sol";

/**
 * @title ERC721AWRefund
 * @dev This contract extends the ERC721A contract and allows users to mint NFTs with a refund option.
 * The contract defines the mint price, maximum mint per user, and maximum mint supply.
 * It also sets a refund period during which users can request a refund for their NFTs.
 * The contract keeps track of refund end timestamps for each NFT and whether an NFT has been refunded.
 * Users can mint NFTs by calling the `safeMint` function and request a refund by calling the `refund` function.
 * The contract owner can withdraw the contract balance after the refund period ends.
 */
contract NFTR is ERC721A, Ownable {
    uint256 public constant mintPrice = 1 ether;
    uint256 public constant maxMintPerUser = 5;
    uint256 public constant maxMintSupply = 100;

    uint256 public constant refundPeriod = 1 minutes;
    uint256 public refundEndTimestamp;

    address public refundAddress;

    mapping(uint256 => uint256) public refundEndTimestamps;
    mapping(uint256 => bool) public hasRefunded;

    /**
     * @dev Constructor function that sets the initial values for the contract.
     * It sets the refund address to the contract address and calculates the refund end timestamp.
     */
    constructor() ERC721A("ERC721AWRefund", "NFTR") Ownable(_msgSender()) {
        refundAddress = address(this);
        refundEndTimestamp = block.timestamp + refundPeriod;
    }

    /**
     * @dev Internal function to override the base URI for the NFTs.
     * @return The base URI for the NFTs.
     */
    function _baseURI() internal pure override returns (string memory) {
        return "ipfs://QmbseRTJWSsLfhsiWwuB2R7EtN93TxfoaMz1S5FXtsFEUB/";
    }

    /**
     * @dev Function to mint NFTs with a refund option.
     * Users need to send enough funds to cover the mint price multiplied by the quantity.
     * The function checks the mint limit per user and the total mint supply.
     * It mints the NFTs, updates the refund end timestamp, and sets the refund end timestamps for the minted NFTs.
     * @param quantity The quantity of NFTs to mint.
     */
    function safeMint(uint256 quantity) public payable {
        require(msg.value >= quantity * mintPrice, "Not enough funds");
        require(
            _numberMinted(msg.sender) + quantity <= maxMintPerUser,
            "Mint Limit"
        );
        require(_totalMinted() + quantity <= maxMintSupply, "SOLD OUT");

        _safeMint(msg.sender, quantity);
        refundEndTimestamp = block.timestamp + refundPeriod;
        for (uint256 i = _currentIndex - quantity; i < _currentIndex; i++) {
            refundEndTimestamps[i] = refundEndTimestamp;
        }
    }

    /**
     * @dev Function to request a refund for a specific NFT.
     * The caller must be the owner of the NFT and the refund period must not have expired.
     * The function transfers the ownership of the NFT to the refund address,
     * marks the NFT as refunded, and refunds the mint price to the caller.
     * @param tokenId The ID of the NFT to refund.
     */
    function refund(uint256 tokenId) external {
        require(
            block.timestamp < getRefundDeadline(tokenId),
            "Refund Period Expired"
        );
        require(msg.sender == ownerOf(tokenId), "Not your NFT");
        uint256 refundAmount = getRefundAmount(tokenId);

        _transfer(msg.sender, refundAddress, tokenId);

        hasRefunded[tokenId] = true;
        Address.sendValue(payable(msg.sender), refundAmount);
    }

    /**
     * @dev Function to get the refund deadline for a specific NFT.
     * If the NFT has already been refunded, the function returns 0.
     * Otherwise, it returns the refund end timestamp for the NFT.
     * @param tokenId The ID of the NFT.
     * @return The refund deadline for the NFT.
     */
    function getRefundDeadline(uint256 tokenId) public view returns (uint256) {
        if (hasRefunded[tokenId]) {
            return 0;
        }
        return refundEndTimestamps[tokenId];
    }

    /**
     * @dev Function to get the refund amount for a specific NFT.
     * If the NFT has already been refunded, the function returns 0.
     * Otherwise, it returns the mint price.
     * @param tokenId The ID of the NFT.
     * @return The refund amount for the NFT.
     */
    function getRefundAmount(uint256 tokenId) public view returns (uint256) {
        if (hasRefunded[tokenId]) {
            return 0;
        }
        return mintPrice;
    }

    /**
     * @dev Function for the contract owner to withdraw the contract balance.
     * The function can only be called after the refund period has ended.
     * It transfers the contract balance to the contract owner.
     */
    function withdraw() external onlyOwner {
        require(
            block.timestamp > refundEndTimestamp,
            "It's not past the refund period"
        );
        uint256 balance = address(this).balance;
        Address.sendValue(payable(msg.sender), balance);
    }
}
